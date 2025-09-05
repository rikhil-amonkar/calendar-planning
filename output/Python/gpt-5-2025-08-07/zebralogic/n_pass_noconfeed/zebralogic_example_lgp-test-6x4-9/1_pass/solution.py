import json
from copy import deepcopy

def solve():
    houses = [1, 2, 3, 4, 5, 6]

    groups = {
        "Name": ["Carol", "Bob", "Alice", "Arnold", "Eric", "Peter"],
        "PhoneModel": ["samsung galaxy s21", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9", "xiaomi mi 11"],
        "Nationality": ["swede", "chinese", "norwegian", "dane", "german", "brit"],
        "Color": ["blue", "red", "yellow", "green", "white", "purple"],
    }

    # Variables are tuples: (group, item)
    variables = []
    for g, items in groups.items():
        for it in items:
            variables.append((g, it))

    # Domains: by default 1..6 for each variable
    domains = {var: set(houses) for var in variables}

    # Helper to create variable ids
    def V(g, it):
        return (g, it)

    # Constraints storage
    constraints = []

    # Constraint registration helpers
    def add_eq(v1, v2):
        constraints.append(("eq", v1, v2, None))

    def add_left_of(v1, v2):
        constraints.append(("lt", v1, v2, None))

    def add_immediately_left_of(v1, v2):
        constraints.append(("immediate_left", v1, v2, None))

    def add_distance(v1, v2, d):
        constraints.append(("distance", v1, v2, d))

    def add_gt(v1, v2):
        constraints.append(("gt", v1, v2, None))

    # Initialize unary domain restrictions from clues
    # 1. Carol is not in the third house.
    domains[V("Name", "Carol")].discard(3)
    # 7. Huawei P50 not in the third house.
    domains[V("PhoneModel", "huawei p50")].discard(3)
    # 8. Samsung Galaxy S21 is in the fifth house.
    domains[V("PhoneModel", "samsung galaxy s21")] = {5}

    # Binary/relational constraints from clues
    # 2. Dane and Brit have one house between them (distance 2).
    add_distance(V("Nationality", "dane"), V("Nationality", "brit"), 2)
    # 3. Carol is the person whose favorite color is green.
    add_eq(V("Name", "Carol"), V("Color", "green"))
    # 4. Arnold is directly left of Alice.
    add_immediately_left_of(V("Name", "Arnold"), V("Name", "Alice"))
    # 5. Alice is the German.
    add_eq(V("Name", "Alice"), V("Nationality", "german"))
    # 6. OnePlus 9 user loves purple.
    add_eq(V("PhoneModel", "oneplus 9"), V("Color", "purple"))
    # 9. White is to the right of Red.
    add_gt(V("Color", "white"), V("Color", "red"))
    # 10. Samsung Galaxy S21 is Bob.
    add_eq(V("PhoneModel", "samsung galaxy s21"), V("Name", "Bob"))
    # 11. Dane loves yellow.
    add_eq(V("Nationality", "dane"), V("Color", "yellow"))
    # 12. S21 is somewhere to the left of Peter.
    add_left_of(V("PhoneModel", "samsung galaxy s21"), V("Name", "Peter"))
    # 13. Peter loves blue.
    add_eq(V("Name", "Peter"), V("Color", "blue"))
    # 14. Peter is the British person.
    add_eq(V("Name", "Peter"), V("Nationality", "brit"))
    # 15. S21 is directly left of iPhone 13.
    add_immediately_left_of(V("PhoneModel", "samsung galaxy s21"), V("PhoneModel", "iphone 13"))
    # 16. Norwegian loves purple.
    add_eq(V("Nationality", "norwegian"), V("Color", "purple"))
    # 17. Xiaomi Mi 11 user is the Chinese.
    add_eq(V("PhoneModel", "xiaomi mi 11"), V("Nationality", "chinese"))

    # Build a mapping from variable to constraints it participates in
    constraints_by_var = {var: [] for var in variables}
    for c in constraints:
        kind, v1, v2, param = c
        constraints_by_var[v1].append(c)
        if v2 is not None:
            constraints_by_var[v2].append(c)

    # All-different will be enforced within each group during search

    # Utility functions for forward checking
    def consistent_binary_constraint(kind, a_var, b_var, a_val, b_val, param=None):
        # Returns True if (a_val,b_val) satisfies the constraint when a_var is first var in constraint definition
        if kind == "eq":
            return a_val == b_val
        elif kind == "lt":
            return a_val < b_val
        elif kind == "gt":
            return a_val > b_val
        elif kind == "immediate_left":
            return a_val + 1 == b_val
        elif kind == "distance":
            return abs(a_val - b_val) == param
        else:
            return True

    def forward_check(var, assignment, domains):
        # Apply all-different for group
        group = var[0]
        val = assignment[var]
        for other in variables:
            if other == var:
                continue
            if other[0] == group and other not in assignment:
                if val in domains[other]:
                    domains[other] = set(x for x in domains[other] if x != val)
                    if not domains[other]:
                        return False

        # For each constraint involving this var, reduce domains of the other var accordingly
        for c in constraints_by_var[var]:
            kind, v1, v2, param = c
            if v2 is None:
                continue

            # Determine roles
            if var == v1:
                other = v2
                role = "first"
            else:
                other = v1
                role = "second"

            # If both assigned, just check consistency
            if other in assignment:
                a_var, b_var = (v1, v2)
                a_val = assignment.get(v1, None)
                b_val = assignment.get(v2, None)
                if a_val is not None and b_val is not None:
                    if not consistent_binary_constraint(kind, a_var, b_var, a_val, b_val, param):
                        return False
                continue

            # Only 'other' unassigned: filter its domain
            new_domain = set(domains[other])
            if kind == "eq":
                # equal positions
                # other must take same value as the assigned var
                new_domain = {assignment[var]} if assignment[var] in new_domain else set()
            elif kind == "lt":
                if role == "first":
                    new_domain = {p for p in new_domain if p > assignment[var]}
                else:
                    new_domain = {p for p in new_domain if p < assignment[var]}
            elif kind == "gt":
                if role == "first":
                    new_domain = {p for p in new_domain if p < assignment[var]}
                else:
                    new_domain = {p for p in new_domain if p > assignment[var]}
            elif kind == "immediate_left":
                if role == "first":
                    needed = assignment[var] + 1
                    new_domain = {needed} if needed in new_domain else set()
                else:
                    needed = assignment[var] - 1
                    new_domain = {needed} if needed in new_domain else set()
            elif kind == "distance":
                # |a - b| = param
                d = param
                poss = set()
                if assignment[var] - d in new_domain:
                    poss.add(assignment[var] - d)
                if assignment[var] + d in new_domain:
                    poss.add(assignment[var] + d)
                new_domain = poss

            if not new_domain:
                return False
            if new_domain != domains[other]:
                domains[other] = new_domain

        return True

    def select_unassigned_var(assignment, domains):
        # Minimum Remaining Values heuristic
        unassigned = [v for v in variables if v not in assignment]
        # break ties by grouping Names first (often helpful), then others
        unassigned.sort(key=lambda v: (len(domains[v]), v[0]))
        return unassigned[0] if unassigned else None

    def is_complete(assignment):
        return len(assignment) == len(variables)

    def is_consistent(assignment):
        # Check all-different in each group
        for g, items in groups.items():
            seen = set()
            for it in items:
                v = (g, it)
                if v in assignment:
                    if assignment[v] in seen:
                        return False
                    seen.add(assignment[v])

        # Check the binary constraints with assigned vars
        for kind, v1, v2, param in constraints:
            if v1 in assignment and v2 in assignment:
                if not consistent_binary_constraint(kind, v1, v2, assignment[v1], assignment[v2], param):
                    return False
        return True

    def backtrack(assignment, domains):
        if is_complete(assignment):
            if is_consistent(assignment):
                return assignment
            return None

        var = select_unassigned_var(assignment, domains)
        if var is None:
            return None

        # Try values in sorted domain
        for value in sorted(domains[var]):
            # Prepare new copies
            new_assignment = dict(assignment)
            new_domains = {v: set(d) for v, d in domains.items()}

            new_assignment[var] = value
            # Reduce domain to singleton for the var
            new_domains[var] = {value}

            # Early all-different check
            if not is_consistent(new_assignment):
                continue

            if not forward_check(var, new_assignment, new_domains):
                continue

            # Additional loop to propagate singletons repeatedly
            changed = True
            while changed:
                changed = False
                # Propagate any variable with singleton domain that is not yet assigned
                singleton_vars = [v for v in variables if v not in new_assignment and len(new_domains[v]) == 1]
                if not singleton_vars:
                    break
                for sv in singleton_vars:
                    sv_val = next(iter(new_domains[sv]))
                    new_assignment[sv] = sv_val
                    if not is_consistent(new_assignment):
                        changed = False
                        break
                    if not forward_check(sv, new_assignment, new_domains):
                        changed = False
                        break
                    changed = True
                if not is_consistent(new_assignment):
                    break
            if not is_consistent(new_assignment):
                continue

            result = backtrack(new_assignment, new_domains)
            if result is not None:
                return result

        return None

    solution_assignment = backtrack({}, domains)
    if solution_assignment is None:
        raise RuntimeError("No solution found")

    # Build house rows
    def house_lookup(group, pos):
        for item in groups[group]:
            if solution_assignment[(group, item)] == pos:
                return item
        return None

    header = ["House", "Name", "PhoneModel", "Nationality", "Color"]
    rows = []
    for h in houses:
        rows.append([
            str(h),
            house_lookup("Name", h),
            house_lookup("PhoneModel", h),
            house_lookup("Nationality", h),
            house_lookup("Color", h),
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve()