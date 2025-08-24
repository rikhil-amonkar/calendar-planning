import json
from copy import deepcopy

# Zebra puzzle solver with constraint propagation and backtracking

HOUSES = {1, 2, 3, 4, 5}

categories = {
    "Name": ["Arnold", "Eric", "Alice", "Bob", "Peter"],
    "Vacation": ["mountain", "city", "cruise", "beach", "camping"],
    "Education": ["doctorate", "high school", "bachelor", "associate", "master"],
    "Color": ["blue", "red", "white", "yellow", "green"],
    "PhoneModel": ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"],
    "Food": ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"],
}

# Create variable keys as "Category:Value"
def var_key(cat, val):
    return f"{cat}:{val}"

all_vars = []
item_to_cat = {}
for cat, vals in categories.items():
    for v in vals:
        k = var_key(cat, v)
        all_vars.append(k)
        item_to_cat[k] = cat

# Union-Find for equality constraints
class UnionFind:
    def __init__(self):
        self.parent = {}

    def find(self, x):
        if x not in self.parent:
            self.parent[x] = x
        # Path compression
        if self.parent[x] != x:
            self.parent[x] = self.find(self.parent[x])
        return self.parent[x]

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.parent[rb] = ra

UF = UnionFind()
for v in all_vars:
    UF.find(v)

# Equality constraints (unify variables)
def unify(a_cat, a_val, b_cat, b_val):
    UF.union(var_key(a_cat, a_val), var_key(b_cat, b_val))

# Apply equalities from clues
# 3. mountain == bachelor's degree
unify("Vacation", "mountain", "Education", "bachelor")
# 8. stir fry == bachelor's degree
unify("Food", "stir fry", "Education", "bachelor")

# 6. Eric == doctorate
unify("Name", "Eric", "Education", "doctorate")
# 9. pizza == doctorate
unify("Food", "pizza", "Education", "doctorate")

# 11. camping == iPhone 13
unify("Vacation", "camping", "PhoneModel", "iphone 13")
# 12. Alice == cruise
unify("Name", "Alice", "Vacation", "cruise")

# 14. Google Pixel 6 == Arnold
unify("PhoneModel", "google pixel 6", "Name", "Arnold")
# 16. Arnold == grilled cheese
unify("Name", "Arnold", "Food", "grilled cheese")

# Build groups
groups = {}
for v in all_vars:
    r = UF.find(v)
    groups.setdefault(r, set()).add(v)

# Initialize domains for groups
group_domains = {g: set(HOUSES) for g in groups}

# Helper to map item to its group
def group_of(cat, val):
    return UF.find(var_key(cat, val))

# Unary constraints (domains)
def remove_from_domain(g, houses_to_remove):
    changed = False
    dom = group_domains[g]
    new_dom = dom - set(houses_to_remove)
    if new_dom != dom:
        group_domains[g] = new_dom
        changed = True
    return changed

def set_domain(g, new_set):
    changed = False
    dom = group_domains[g]
    new_dom = dom & set(new_set)
    if new_dom != dom:
        group_domains[g] = new_dom
        changed = True
    return changed

# Apply unary constraints from clues
# 5. Samsung Galaxy S21 is in the third house.
set_domain(group_of("PhoneModel", "samsung galaxy s21"), {3})
# 7. Doctorate in the third house.
set_domain(group_of("Education", "doctorate"), {3})
# 1. Stew is not in the first house.
remove_from_domain(group_of("Food", "stew"), {1})
# 13. One house between high school and S21 -> implies HS in {1,5} since S21=3
set_domain(group_of("Education", "high school"), {1, 5})
# 17. Grilled cheese not in the fourth house.
remove_from_domain(group_of("Food", "grilled cheese"), {4})
# 20. Green not in the second house.
remove_from_domain(group_of("Color", "green"), {2})
# 4. Doctorate to the right of Bob -> Bob cannot be 3,4,5? Doctorate=3 so Bob<3
set_domain(group_of("Name", "Bob"), {1, 2})
# 21 and 10 imply Peter cannot be 4 or 5 (needs two colors to the right)
set_domain(group_of("Name", "Peter"), {1, 2, 3})
# Also Name:Eric must be at 3 (due to equal to doctorate)
set_domain(group_of("Name", "Eric"), {3})
# Pizza already unified with doctorate -> {3}
set_domain(group_of("Food", "pizza"), {3})

# Build category to groups map for AllDifferent
category_groups = {cat: set() for cat in categories}
for cat, vals in categories.items():
    for v in vals:
        category_groups[cat].add(group_of(cat, v))

# Binary constraints
# Represented as tuples: (type, A_group, B_group, param)
# type in {"diff_eq", "right_of"}

constraints = []

def add_diff_eq(cat1, val1, cat2, val2, k):
    constraints.append(("diff_eq", group_of(cat1, val1), group_of(cat2, val2), k))

def add_right_of(cat1, val1, cat2, val2):
    constraints.append(("right_of", group_of(cat1, val1), group_of(cat2, val2), None))

# 2. Two houses between stir fry and associate's degree (and stir fry == bachelor).
add_diff_eq("Food", "stir fry", "Education", "associate", 3)
# 18. Two houses between bachelor's degree and red.
add_diff_eq("Education", "bachelor", "Color", "red", 3)
# 4. Doctorate to the right of Bob.
add_right_of("Education", "doctorate", "Name", "Bob")
# 10. Green to the right of Peter.
add_right_of("Color", "green", "Name", "Peter")
# 21. Blue to the right of Peter.
add_right_of("Color", "blue", "Name", "Peter")
# 13. One house between HS and S21.
add_diff_eq("Education", "high school", "PhoneModel", "samsung galaxy s21", 2)
# 15. OnePlus 9 to right of Huawei P50.
add_right_of("PhoneModel", "oneplus 9", "PhoneModel", "huawei p50")
# 19. Beach to right of City.
add_right_of("Vacation", "beach", "Vacation", "city")
# 22. One house between camping and yellow.
add_diff_eq("Vacation", "camping", "Color", "yellow", 2)

# Propagation functions
def all_different_propagate(domains):
    changed = False
    for cat, group_set in category_groups.items():
        # Collect assigned houses in this category
        assigned = {}
        for g in group_set:
            if len(domains[g]) == 1:
                h = next(iter(domains[g]))
                assigned[g] = h
        # Remove assigned houses from others in the same category
        taken = set(assigned.values())
        for g in group_set:
            if len(domains[g]) != 1:
                new_dom = domains[g] - taken
                if new_dom != domains[g]:
                    domains[g] = new_dom
                    changed = True
    return changed

def apply_right_of(domains, A, B):
    # A > B
    DA = domains[A]
    DB = domains[B]
    if not DA or not DB:
        return False
    changed = False
    minB = min(DB)
    maxA = max(DA)
    # Prune A: must be greater than some b in DB -> a > min(DB)
    new_DA = set([a for a in DA if a > minB])
    # Prune B: must be less than some a in DA -> b < max(DA)
    new_DB = set([b for b in DB if b < maxA])
    if new_DA != DA:
        domains[A] = new_DA
        changed = True
    if new_DB != DB:
        domains[B] = new_DB
        changed = True
    return changed

def apply_diff_eq(domains, A, B, k):
    # |A - B| = k
    DA = domains[A]
    DB = domains[B]
    if not DA or not DB:
        return False
    changed = False
    # Allowed A values are those that are within k of some B
    allowed_A = set()
    for b in DB:
        if 1 <= b - k <= 5:
            allowed_A.add(b - k)
        if 1 <= b + k <= 5:
            allowed_A.add(b + k)
    new_DA = DA & allowed_A
    if new_DA != DA:
        domains[A] = new_DA
        changed = True
    # Allowed B values are those that are within k of some A
    allowed_B = set()
    for a in DA:
        if 1 <= a - k <= 5:
            allowed_B.add(a - k)
        if 1 <= a + k <= 5:
            allowed_B.add(a + k)
    new_DB = DB & allowed_B
    if new_DB != DB:
        domains[B] = new_DB
        changed = True
    return changed

def propagate(domains):
    changed = True
    while changed:
        changed = False
        # AllDifferent propagation
        if all_different_propagate(domains):
            changed = True
        # Binary constraints propagation
        for ctype, A, B, param in constraints:
            if ctype == "right_of":
                if apply_right_of(domains, A, B):
                    changed = True
            elif ctype == "diff_eq":
                if apply_diff_eq(domains, A, B, param):
                    changed = True
        # Check for domain wipeout
        for g, d in domains.items():
            if len(d) == 0:
                return False
    return True

# Initial propagation
if not propagate(group_domains):
    raise RuntimeError("Inconsistent initial constraints")

# Backtracking search
def is_complete(domains):
    return all(len(d) == 1 for d in domains.values())

def select_unassigned_group(domains):
    # Minimum Remaining Values heuristic
    candidates = [(len(d), g) for g, d in domains.items() if len(d) > 1]
    if not candidates:
        return None
    candidates.sort()
    return candidates[0][1]

def consistent(domains):
    # AllDifferent check per category (quick check)
    for cat, group_set in category_groups.items():
        seen = {}
        for g in group_set:
            if len(domains[g]) == 1:
                h = next(iter(domains[g]))
                if h in seen and seen[h] != g:
                    return False
                seen[h] = g
    # For binary constraints, check only when both assigned
    for ctype, A, B, param in constraints:
        if len(domains[A]) == 1 and len(domains[B]) == 1:
            a = next(iter(domains[A]))
            b = next(iter(domains[B]))
            if ctype == "right_of":
                if not (a > b):
                    return False
            elif ctype == "diff_eq":
                if not (abs(a - b) == param):
                    return False
    return True

def search(domains):
    if not consistent(domains):
        return None
    if is_complete(domains):
        return domains
    g = select_unassigned_group(domains)
    if g is None:
        return None
    # Try values in domain
    for val in sorted(domains[g]):
        new_domains = deepcopy(domains)
        new_domains[g] = {val}
        if not propagate(new_domains):
            continue
        res = search(new_domains)
        if res is not None:
            return res
    return None

solution_domains = search(group_domains)
if solution_domains is None:
    raise RuntimeError("No solution found")

# Build final house-by-house assignment
# For each house, for each category, find the unique value whose group is assigned to that house
assignment = {g: next(iter(d)) for g, d in solution_domains.items()}

house_rows = {i: {} for i in range(1, 6)}
for cat, vals in categories.items():
    for v in vals:
        g = group_of(cat, v)
        h = assignment[g]
        house_rows[h][cat] = v

# Compose JSON output
header = ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"]
rows = []
for h in range(1, 6):
    row = [
        str(h),
        house_rows[h]["Name"],
        house_rows[h]["Vacation"],
        house_rows[h]["Education"],
        house_rows[h]["Color"],
        house_rows[h]["PhoneModel"],
        house_rows[h]["Food"],
    ]
    rows.append(row)

output = {
    "solution": {
        "header": header,
        "rows": rows
    }
}

print(json.dumps(output, ensure_ascii=False))