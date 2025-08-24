import json
from copy import deepcopy

# Define categories and values
categories = {
    "Name": ["Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"],
    "Cigar": ["pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"],
    "Music": ["hip hop", "jazz", "country", "pop", "classical", "rock"],
    "Drink": ["water", "milk", "boba tea", "tea", "root beer", "coffee"],
    "Mother": ["Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"],
    "Food": ["soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"],
}

houses = set(range(1, 7))  # 1..6

# Initialize domains: for each (category, value) pair, domain is {1..6}
domains = {}
for cat, vals in categories.items():
    for v in vals:
        domains[(cat, v)] = set(houses)

# Constraint classes
class Constraint:
    def propagate(self, domains):
        return False

class AllDifferentConstraint(Constraint):
    def __init__(self, category, values):
        self.category = category
        self.values = values

    def propagate(self, domains):
        changed = False
        # Singleton pruning: if a value in this category is assigned to a house,
        # remove that house from other values' domains.
        singletons = {next(iter(domains[(self.category, v)]))
                      for v in self.values if len(domains[(self.category, v)]) == 1}
        for v in self.values:
            dom = domains[(self.category, v)]
            if len(dom) == 1:
                continue
            before = set(dom)
            dom.difference_update(singletons)
            if dom != before:
                changed = True
        return changed

class EqualConstraint(Constraint):
    def __init__(self, a, b):
        self.a = a  # (cat, val)
        self.b = b

    def propagate(self, domains):
        da = domains[self.a]
        db = domains[self.b]
        inter = da & db
        changed = False
        if inter != da:
            domains[self.a] = set(inter)
            changed = True
        if inter != db:
            domains[self.b] = set(inter)
            changed = True
        return changed

class NotInConstraint(Constraint):
    def __init__(self, a, house):
        self.a = a
        self.house = house

    def propagate(self, domains):
        dom = domains[self.a]
        if self.house in dom:
            dom.remove(self.house)
            return True
        return False

class InConstraint(Constraint):
    def __init__(self, a, house):
        self.a = a
        self.house = house

    def propagate(self, domains):
        dom = domains[self.a]
        if dom != {self.house}:
            domains[self.a] = {self.house}
            return True
        return False

class NextLeftConstraint(Constraint):
    # pos(a) = pos(b) - 1
    def __init__(self, a, b):
        self.a = a
        self.b = b

    def propagate(self, domains):
        da = domains[self.a]
        db = domains[self.b]
        changed = False

        # A cannot be in last house; B cannot be in first
        before = set(da)
        da.intersection_update(set(h for h in da if h + 1 in db))
        if da != before:
            changed = True

        before = set(db)
        db.intersection_update(set(h for h in db if h - 1 in da))
        if db != before:
            changed = True

        # Also ensure bounds
        if 6 in da:
            da.remove(6)
            changed = True
        if 1 in db:
            db.remove(1)
            changed = True

        # Second pass to enforce mutual support
        before = set(da)
        da.intersection_update(set(h for h in da if (h + 1) in db))
        if da != before:
            changed = True

        before = set(db)
        db.intersection_update(set(h for h in db if (h - 1) in da))
        if db != before:
            changed = True

        return changed

class SomewhereLeftConstraint(Constraint):
    # pos(a) < pos(b)
    def __init__(self, a, b):
        self.a = a
        self.b = b

    def propagate(self, domains):
        da = domains[self.a]
        db = domains[self.b]
        changed = False

        # For each h in da, there must be some k in db with k>h
        before = set(da)
        da.intersection_update(set(h for h in da if any(k > h for k in db)))
        if da != before:
            changed = True

        # For each k in db, there must be some h in da with h<k
        before = set(db)
        db.intersection_update(set(k for k in db if any(h < k for h in da)))
        if db != before:
            changed = True

        return changed

class DistanceConstraint(Constraint):
    # abs(pos(a) - pos(b)) == dist
    def __init__(self, a, b, dist):
        self.a = a
        self.b = b
        self.dist = dist

    def propagate(self, domains):
        da = domains[self.a]
        db = domains[self.b]
        d = self.dist
        changed = False

        before = set(da)
        da.intersection_update(set(h for h in da if (h + d in db) or (h - d in db)))
        if da != before:
            changed = True

        before = set(db)
        db.intersection_update(set(h for h in db if (h + d in da) or (h - d in da)))
        if db != before:
            changed = True

        return changed

# Build constraints list
constraints = []

# All-different per category
for cat, vals in categories.items():
    constraints.append(AllDifferentConstraint(cat, vals))

# Helper functions to get item keys
def N(name): return ("Name", name)
def C(cigar): return ("Cigar", cigar)
def M(music): return ("Music", music)
def D(drink): return ("Drink", drink)
def Mo(mother): return ("Mother", mother)
def F(food): return ("Food", food)

# Apply clues as constraints

# 1. Carol is directly left of the person who loves eating grilled cheese.
constraints.append(NextLeftConstraint(N("Carol"), F("grilled cheese")))

# 2. Eric is not in the second house.
constraints.append(NotInConstraint(N("Eric"), 2))

# 3. The person whose mother's name is Holly is somewhere to the right of Carol.
constraints.append(SomewhereLeftConstraint(N("Carol"), Mo("Holly")))

# 4. The person who loves eating grilled cheese is somewhere to the right of the person who loves rock music.
constraints.append(SomewhereLeftConstraint(M("rock"), F("grilled cheese")))

# 5. Eric is directly left of Carol.
constraints.append(NextLeftConstraint(N("Eric"), N("Carol")))

# 6. The person who loves pop music is not in the third house.
constraints.append(NotInConstraint(M("pop"), 3))

# 7. Eric is the person who loves country music.
constraints.append(EqualConstraint(N("Eric"), M("country")))

# 8. The person who loves classical music is in the sixth house.
constraints.append(InConstraint(M("classical"), 6))

# 9. The coffee drinker is Bob.
constraints.append(EqualConstraint(D("coffee"), N("Bob")))

# 10. The person who smokes many unique blends is Peter.
constraints.append(EqualConstraint(C("blends"), N("Peter")))

# 11. The person who loves the stew is not in the fifth house.
constraints.append(NotInConstraint(F("stew"), 5))

# 12. The root beer lover is directly left of The person whose mother's name is Janelle.
constraints.append(NextLeftConstraint(D("root beer"), Mo("Janelle")))

# 13. There are two houses between The person whose mother's name is Sarah and the person who smokes Yellow Monster.
constraints.append(DistanceConstraint(Mo("Sarah"), C("yellow monster"), 3))

# 14. Eric is the tea drinker.
constraints.append(EqualConstraint(N("Eric"), D("tea")))

# 15. The person partial to Pall Mall is somewhere to the right of the person who loves stir fry.
constraints.append(SomewhereLeftConstraint(F("stir fry"), C("pall mall")))

# 16. The person who loves the soup is Bob.
constraints.append(EqualConstraint(F("soup"), N("Bob")))

# 17. The person who loves hip-hop music is directly left of The person whose mother's name is Kailyn.
constraints.append(NextLeftConstraint(M("hip hop"), Mo("Kailyn")))

# 18. Arnold is somewhere to the right of The person whose mother's name is Kailyn.
constraints.append(SomewhereLeftConstraint(Mo("Kailyn"), N("Arnold")))

# 19. The one who only drinks water is directly left of the person who smokes Blue Master.
constraints.append(NextLeftConstraint(D("water"), C("blue master")))

# 20. The person who loves the spaghetti eater is somewhere to the left of the person who smokes many unique blends.
# Interpreted as: spaghetti is somewhere to the left of blends.
constraints.append(SomewhereLeftConstraint(F("spaghetti"), C("blends")))

# 21. The person whose mother's name is Sarah is directly left of the person who loves jazz music.
constraints.append(NextLeftConstraint(Mo("Sarah"), M("jazz")))

# 22. The person who loves hip-hop music is directly left of the root beer lover.
constraints.append(NextLeftConstraint(M("hip hop"), D("root beer")))

# 23. The one who only drinks water is the person who loves the stew.
constraints.append(EqualConstraint(D("water"), F("stew")))

# 24. The Dunhill smoker is not in the second house.
constraints.append(NotInConstraint(C("dunhill"), 2))

# 25. The person who likes milk is The person whose mother's name is Janelle.
constraints.append(EqualConstraint(D("milk"), Mo("Janelle")))

# 26. Eric is The person whose mother's name is Aniya.
constraints.append(EqualConstraint(N("Eric"), Mo("Aniya")))

# Derived equality from 17 and 22: the house to the right of hip hop has both Mother=Kailyn and Drink=root beer,
# hence Mother=Kailyn is the root beer drinker.
constraints.append(EqualConstraint(Mo("Kailyn"), D("root beer")))

# Solver functions
def propagate_all(domains):
    changed = True
    while changed:
        changed = False
        for cons in constraints:
            if cons.propagate(domains):
                changed = True
        # Check for empty domains -> early fail
        for k, dom in domains.items():
            if len(dom) == 0:
                return False
    return True

def is_solved(domains):
    return all(len(dom) == 1 for dom in domains.values())

def choose_var(domains):
    # Choose variable with smallest domain > 1
    best = None
    best_size = 999
    for k, dom in domains.items():
        if 1 < len(dom) < best_size:
            best = k
            best_size = len(dom)
    return best

def backtrack(domains):
    if not propagate_all(domains):
        return None
    if is_solved(domains):
        return domains
    var = choose_var(domains)
    if var is None:
        return None
    dom_values = sorted(domains[var])
    for h in dom_values:
        new_domains = deepcopy(domains)
        new_domains[var] = {h}
        result = backtrack(new_domains)
        if result is not None:
            return result
    return None

solution_domains = backtrack(deepcopy(domains))
if solution_domains is None:
    raise RuntimeError("No solution found")

# Build mapping from (category, value) -> house (int)
positions = {k: next(iter(v)) for k, v in solution_domains.items()}

# Build rows per house
header = ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"]
rows = []
for h in range(1, 7):
    # Find value for each category at house h
    name = next(val for val in categories["Name"] if positions[("Name", val)] == h)
    cigar = next(val for val in categories["Cigar"] if positions[("Cigar", val)] == h)
    music = next(val for val in categories["Music"] if positions[("Music", val)] == h)
    drink = next(val for val in categories["Drink"] if positions[("Drink", val)] == h)
    mother = next(val for val in categories["Mother"] if positions[("Mother", val)] == h)
    food = next(val for val in categories["Food"] if positions[("Food", val)] == h)
    rows.append([str(h), name, cigar, music, drink, mother, food])

output = {
    "solution": {
        "header": header,
        "rows": rows
    }
}

print(json.dumps(output, ensure_ascii=False))