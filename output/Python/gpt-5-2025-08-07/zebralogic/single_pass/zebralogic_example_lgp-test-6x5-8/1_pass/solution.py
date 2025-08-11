import json
from itertools import product

# Define categories and values
categories = {
    "name": ["Arnold", "Peter", "Bob", "Eric", "Carol", "Alice"],
    "animals": ["horse", "rabbit", "fish", "cat", "bird", "dog"],
    "occupation": ["engineer", "nurse", "lawyer", "teacher", "artist", "doctor"],
    "sports": ["basketball", "volleyball", "soccer", "tennis", "baseball", "swimming"],
    "heights": ["average", "tall", "short", "very short", "very tall", "super tall"],
}

houses = list(range(6))  # 0..5 for houses 1..6

# Variable is a tuple (category, value)
def var(cat, val):
    return (cat, val)

# All variables
variables = []
for cat, vals in categories.items():
    for v in vals:
        variables.append(var(cat, v))

# Constraints
class Constraint:
    def __init__(self, kind, a, b=None):
        self.kind = kind  # 'eq', 'lt', 'gt', 'adj'
        self.a = a
        self.b = b

    def check(self, assignment):
        # Return True if constraint is satisfied or not yet decidable; False if violated
        if self.kind == 'eq':
            pa = assignment.get(self.a)
            pb = assignment.get(self.b)
            if pa is not None and pb is not None:
                return pa == pb
            return True
        elif self.kind == 'lt':
            pa = assignment.get(self.a)
            pb = assignment.get(self.b)
            if pa is not None and pb is not None:
                return pa < pb
            # Partial: if one side at boundary making impossible
            if pa is not None and pa == 5:
                return False
            if pb is not None and pb == 0:
                return False
            return True
        elif self.kind == 'gt':
            pa = assignment.get(self.a)
            pb = assignment.get(self.b)
            if pa is not None and pb is not None:
                return pa > pb
            if pa is not None and pa == 0:
                return False
            if pb is not None and pb == 5:
                return False
            return True
        elif self.kind == 'adj':  # a directly left of b -> pa + 1 == pb
            pa = assignment.get(self.a)
            pb = assignment.get(self.b)
            if pa is not None and pb is not None:
                return pa + 1 == pb
            if pa is not None:
                # if a is last, cannot be left of any
                if pa == 5:
                    return False
            if pb is not None:
                # if b is first, no left neighbor
                if pb == 0:
                    return False
            return True
        else:
            return True

    def domain_filter(self, var_to_filter, assignment):
        # Return a set of allowed positions adjustment for var_to_filter based on current assignment
        # or None if no additional restriction
        if self.kind == 'eq':
            if var_to_filter == self.a:
                pb = assignment.get(self.b)
                if pb is not None:
                    return {pb}
            elif var_to_filter == self.b:
                pa = assignment.get(self.a)
                if pa is not None:
                    return {pa}
        elif self.kind == 'lt':
            if var_to_filter == self.a:
                pb = assignment.get(self.b)
                if pb is not None:
                    return set(range(0, pb))
            elif var_to_filter == self.b:
                pa = assignment.get(self.a)
                if pa is not None:
                    return set(range(pa + 1, 6))
        elif self.kind == 'gt':
            if var_to_filter == self.a:
                pb = assignment.get(self.b)
                if pb is not None:
                    return set(range(pb + 1, 6))
            elif var_to_filter == self.b:
                pa = assignment.get(self.a)
                if pa is not None:
                    return set(range(0, pa))
        elif self.kind == 'adj':
            if var_to_filter == self.a:
                pb = assignment.get(self.b)
                if pb is not None:
                    if pb - 1 >= 0:
                        return {pb - 1}
                    else:
                        return set()  # impossible
            elif var_to_filter == self.b:
                pa = assignment.get(self.a)
                if pa is not None:
                    if pa + 1 <= 5:
                        return {pa + 1}
                    else:
                        return set()
        return None

constraints = []

# Build constraints from clues

# 1. engineer == dog
constraints.append(Constraint('eq', var('occupation','engineer'), var('animals','dog')))
# 2. average left of short
constraints.append(Constraint('lt', var('heights','average'), var('heights','short')))
# 3. average directly left of rabbit
constraints.append(Constraint('adj', var('heights','average'), var('animals','rabbit')))
# 4. tall left of very short
constraints.append(Constraint('lt', var('heights','tall'), var('heights','very short')))
# 5. Arnold == cat
constraints.append(Constraint('eq', var('name','Arnold'), var('animals','cat')))
# 6. horse == teacher
constraints.append(Constraint('eq', var('animals','horse'), var('occupation','teacher')))
# 7. Carol == soccer
constraints.append(Constraint('eq', var('name','Carol'), var('sports','soccer')))
# 8. tall == volleyball
constraints.append(Constraint('eq', var('heights','tall'), var('sports','volleyball')))
# 10. tennis == teacher
constraints.append(Constraint('eq', var('sports','tennis'), var('occupation','teacher')))
# 11. average == swimming
constraints.append(Constraint('eq', var('heights','average'), var('sports','swimming')))
# 12. baseball directly left of engineer
constraints.append(Constraint('adj', var('sports','baseball'), var('occupation','engineer')))
# 13. Peter == nurse
constraints.append(Constraint('eq', var('name','Peter'), var('occupation','nurse')))
# 14. Bob right of artist
constraints.append(Constraint('gt', var('name','Bob'), var('occupation','artist')))
# 15. teacher directly left of soccer
constraints.append(Constraint('adj', var('occupation','teacher'), var('sports','soccer')))
# 16. rabbit == Alice
constraints.append(Constraint('eq', var('animals','rabbit'), var('name','Alice')))
# 17. fish == Carol
constraints.append(Constraint('eq', var('animals','fish'), var('name','Carol')))
# 19. cat right of very short
constraints.append(Constraint('gt', var('animals','cat'), var('heights','very short')))

# Fixed positions:
fixed_positions = {
    var('occupation','lawyer'): 4,        # 9
    var('heights','super tall'): 4,       # 20
    var('sports','baseball'): 0,          # 18
    var('occupation','engineer'): 1,      # 12 + 18
    var('animals','dog'): 1,              # 1
}

# Static domain restrictions to help pruning
static_forbidden = {
    var('sports','soccer'): {0},                  # must have teacher to the left
    var('occupation','teacher'): {5},             # must be left of soccer
    var('heights','average'): {5},                # must be left of rabbit
    var('animals','rabbit'): {0},                 # has average to the left
    var('animals','cat'): {0},                    # must be right of very short
    var('name','Bob'): {0},                       # must be right of artist
    var('occupation','artist'): {5},              # must be left of Bob
    var('sports','swimming'): {5},                # equals average
    var('sports','volleyball'): {5},              # equals tall which is left of very short
    var('sports','tennis'): {5},                  # equals teacher which is left of soccer
    var('name','Arnold'): {0},                    # equals cat owner, which isn't 0
    var('name','Alice'): {0},                     # equals rabbit owner, which isn't 0
    var('name','Carol'): {0},                     # equals soccer which isn't 0
    var('heights','short'): {0},                  # average < short
    var('heights','very short'): {0},             # tall < very short
}

# All-different constraints are handled by domain filtering (no two values in same category can share a position)

# Prepare data structures
all_vars = variables[:]
assignment = {}

# Apply fixed positions
for k, v in fixed_positions.items():
    assignment[k] = v

# Helper to get used positions per category
def used_positions(cat, assignment):
    used = set()
    for (c, v), pos in assignment.items():
        if c == cat:
            used.add(pos)
    return used

# Get domain for a variable given current assignment
def get_domain(var_key, assignment):
    cat, val = var_key
    # base domain: all houses
    dom = set(houses)
    # apply category used positions (all-different)
    dom -= used_positions(cat, assignment)
    # apply static forbidden
    if var_key in static_forbidden:
        dom -= static_forbidden[var_key]
    # apply fixed if any
    if var_key in fixed_positions:
        dom &= {fixed_positions[var_key]}

    # apply dynamic constraint propagation against other assigned vars
    for cons in constraints:
        if cons.a == var_key or cons.b == var_key:
            other = cons.b if cons.a == var_key else cons.a
            filt = cons.domain_filter(var_key, assignment)
            if filt is not None:
                dom &= set(filt)
            # Early exit if empty
            if not dom:
                return set()
    return dom

# Check all constraints not violated
def constraints_ok(assignment):
    for cons in constraints:
        if not cons.check(assignment):
            return False
    return True

# Variable ordering: MRV (minimum remaining values)
def select_unassigned_var(assignment):
    unassigned = [v for v in all_vars if v not in assignment]
    # Prefer ones with fixed positions/domains first
    best_var = None
    best_domain = None
    best_size = 10**9
    for v in unassigned:
        dom = get_domain(v, assignment)
        size = len(dom)
        if size < best_size:
            best_size = size
            best_var = v
            best_domain = dom
        if size == 0:
            return v, set()  # immediate failure
    return best_var, best_domain

solution_assignment = None

def backtrack(assignment):
    global solution_assignment
    if len(assignment) == len(all_vars):
        if constraints_ok(assignment):
            solution_assignment = dict(assignment)
            return True
        return False
    var_key, domain = select_unassigned_var(assignment)
    if not domain:
        return False
    # Try ordered domain
    for val in sorted(domain):
        assignment[var_key] = val
        if constraints_ok(assignment):
            if backtrack(assignment):
                return True
        del assignment[var_key]
    return False

# Run the solver
backtrack(assignment)

# Build output
if solution_assignment is None:
    output = {
        "solution": {
            "header": ["House", "name", "animals", "occupation", "sports", "heights"],
            "rows": []
        },
        "status": "no solution found"
    }
else:
    # Build reverse maps pos -> value for each category
    pos_to_value = {cat: [None]*6 for cat in categories}
    for (cat, val), pos in solution_assignment.items():
        pos_to_value[cat][pos] = val

    rows = []
    for i in range(6):
        row = [
            str(i+1),
            pos_to_value["name"][i],
            pos_to_value["animals"][i],
            pos_to_value["occupation"][i],
            pos_to_value["sports"][i],
            pos_to_value["heights"][i],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "name", "animals", "occupation", "sports", "heights"],
            "rows": rows
        }
    }

print(json.dumps(output, indent=2))