import json

def solve():
    # Define categories and items
    categories = {
        "Name": ["Arnold", "Eric", "Alice", "Bob", "Peter"],
        "Vacation": ["mountain", "city", "cruise", "beach", "camping"],
        "Education": ["doctorate", "high school", "bachelor", "associate", "master"],
        "Color": ["blue", "red", "white", "yellow", "green"],
        "PhoneModel": ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"],
        "Food": ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]
    }

    houses = list(range(5))  # positions 0..4 represent houses 1..5

    def V(cat, item):
        return (cat, item)

    # All variables: one per item across all categories
    variables = []
    for cat, items in categories.items():
        for it in items:
            variables.append(V(cat, it))

    # Base domains
    base_domain = {var: set(houses) for var in variables}

    # Fixed positions (indexing 0..4)
    fixed = {
        V("PhoneModel", "samsung galaxy s21"): 2,  # Clue 5
        V("Education", "doctorate"): 2,            # Clues 7
    }

    # Not-at constraints (forbidden positions)
    not_at = {
        V("Food", "stew"): {0},                   # Clue 1
        V("Food", "grilled cheese"): {3},         # Clue 17 (not in fourth house -> index 3)
        V("Color", "green"): {1},                 # Clue 20 (not in second house -> index 1)
    }

    # Equalities (same person/house)
    equalities = [
        (V("Vacation", "mountain"), V("Education", "bachelor")),           # Clue 3
        (V("Food", "stir fry"), V("Education", "bachelor")),               # Clue 8 (and with 3 implies mountain=stir fry=bachelor)
        (V("Name", "Eric"), V("Education", "doctorate")),                  # Clue 6
        (V("Food", "pizza"), V("Education", "doctorate")),                 # Clue 9
        (V("Name", "Alice"), V("Vacation", "cruise")),                     # Clue 12
        (V("PhoneModel", "google pixel 6"), V("Name", "Arnold")),          # Clue 14
        (V("Food", "grilled cheese"), V("Name", "Arnold")),                # Clue 16
        (V("Vacation", "camping"), V("PhoneModel", "iphone 13")),          # Clue 11
    ]

    # Right-of constraints: A > B
    right_of = [
        (V("Education", "doctorate"), V("Name", "Bob")),         # Clue 4
        (V("Color", "green"), V("Name", "Peter")),               # Clue 10
        (V("Color", "blue"), V("Name", "Peter")),                # Clue 21
        (V("PhoneModel", "oneplus 9"), V("PhoneModel", "huawei p50")),  # Clue 15
        (V("Vacation", "beach"), V("Vacation", "city")),         # Clue 19
    ]

    # Exact distance constraints: |A - B| == d
    distance_eq = [
        (V("Food", "stir fry"), V("Education", "associate"), 3),      # Clue 2
        (V("Education", "bachelor"), V("Color", "red"), 3),           # Clue 18
        (V("Education", "high school"), V("PhoneModel", "samsung galaxy s21"), 2),  # Clue 13
        (V("Vacation", "camping"), V("Color", "yellow"), 2),          # Clue 22
    ]

    # Initialize domains with fixed and not-at constraints
    for var, pos in fixed.items():
        base_domain[var] = {pos}
    for var, forbids in not_at.items():
        base_domain[var] -= forbids

    # Helper: categories -> items for all-different checks
    category_items = {cat: [V(cat, it) for it in items] for cat, items in categories.items()}

    # Backtracking solver
    def propagate_equalities(assignment):
        # Propagate equalities until no change; return False if inconsistency
        changed = True
        while changed:
            changed = False
            for a, b in equalities:
                av = assignment.get(a)
                bv = assignment.get(b)
                if av is not None and bv is not None:
                    if av != bv:
                        return False
                elif av is not None and bv is None:
                    assignment[b] = av
                    changed = True
                elif av is None and bv is not None:
                    assignment[a] = bv
                    changed = True
        return True

    def check_all_different(assignment):
        for cat, items in category_items.items():
            seen = {}
            for var in items:
                if var in assignment:
                    pos = assignment[var]
                    if pos in seen:
                        return False
                    seen[pos] = var
        return True

    def check_constraints(assignment):
        # Fixed positions
        for var, pos in fixed.items():
            if var in assignment and assignment[var] != pos:
                return False

        # Not-at constraints
        for var, forbids in not_at.items():
            if var in assignment and assignment[var] in forbids:
                return False

        # Equalities
        for a, b in equalities:
            if a in assignment and b in assignment and assignment[a] != assignment[b]:
                return False

        # Right-of
        for a, b in right_of:
            if a in assignment and b in assignment:
                if not (assignment[a] > assignment[b]):
                    return False

        # Distances
        for a, b, d in distance_eq:
            if a in assignment and b in assignment:
                if abs(assignment[a] - assignment[b]) != d:
                    return False

        # All-different per category
        if not check_all_different(assignment):
            return False

        return True

    def domain_for(var, assignment):
        # Start with base domain
        dom = set(base_domain[var])

        # Enforce all-different in same category: remove positions already taken by other items in same category
        cat = var[0]
        for other in category_items[cat]:
            if other != var and other in assignment:
                if assignment[other] in dom:
                    dom.remove(assignment[other])

        # Equality constraints
        for a, b in equalities:
            if var == a and b in assignment:
                dom &= {assignment[b]}
            elif var == b and a in assignment:
                dom &= {assignment[a]}

        # Fixed, already handled in base_domain

        # Not-at constraints, already applied to base_domain but re-apply for safety
        if var in not_at:
            dom -= not_at[var]

        # Right-of constraints directional domain pruning
        for a, b in right_of:
            if var == a and b in assignment:
                dom = {p for p in dom if p > assignment[b]}
            elif var == b and a in assignment:
                dom = {p for p in dom if p < assignment[a]}

        # Distance constraints domain pruning
        for a, b, d in distance_eq:
            if var == a and b in assignment:
                dom = {p for p in dom if abs(p - assignment[b]) == d}
            elif var == b and a in assignment:
                dom = {p for p in dom if abs(p - assignment[a]) == d}

        return dom

    def select_unassigned_var(assignment):
        # Minimum remaining values heuristic
        best_var = None
        best_domain = None
        best_size = 999
        for var in variables:
            if var not in assignment:
                dom = domain_for(var, assignment)
                size = len(dom)
                if size == 0:
                    return var, dom  # immediate failure
                if size < best_size:
                    best_size = size
                    best_var = var
                    best_domain = dom
                    if best_size == 1:
                        break
        return best_var, best_domain

    def backtrack(assignment):
        # Propagate equalities
        if not propagate_equalities(assignment):
            return None

        if not check_constraints(assignment):
            return None

        if len(assignment) == len(variables):
            return assignment

        var, dom = select_unassigned_var(assignment)
        if var is None:
            return assignment  # All assigned

        # If domain is empty, fail
        if len(dom) == 0:
            return None

        # Try values in domain
        for val in sorted(dom):
            new_assignment = assignment.copy()
            new_assignment[var] = val
            result = backtrack(new_assignment)
            if result is not None:
                return result
        return None

    # Seed assignment with fixed variables (and propagate equalities)
    assignment = {}
    for var, pos in fixed.items():
        assignment[var] = pos
    # Also propagate equalities so that doctorates propagate to Eric and Pizza, etc.
    solution_assignment = backtrack(assignment)
    if solution_assignment is None:
        raise RuntimeError("No solution found")

    # Invert to per-house rows
    # Build pos -> item for each category
    pos_map = {cat: {i: None for i in houses} for cat in categories.keys()}
    for cat, items in categories.items():
        for it in items:
            var = V(cat, it)
            pos = solution_assignment[var]
            pos_map[cat][pos] = it

    header = ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"]
    rows = []
    for i in houses:
        rows.append([
            str(i + 1),
            pos_map["Name"][i],
            pos_map["Vacation"][i],
            pos_map["Education"][i],
            pos_map["Color"][i],
            pos_map["PhoneModel"][i],
            pos_map["Food"][i],
        ])

    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, ensure_ascii=False))