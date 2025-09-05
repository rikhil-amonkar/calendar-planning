import json
from collections import deque, defaultdict

def solve_puzzle():
    # Houses are 1..5 (left to right)
    houses = list(range(1, 6))

    # Categories and values
    Names = ["Bob", "Eric", "Arnold", "Alice", "Peter"]
    Colors = ["blue", "green", "white", "yellow", "red"]
    PhoneModels = ["huawei p50", "samsung galaxy s21", "oneplus 9", "iphone 13", "google pixel 6"]
    Occupations = ["artist", "teacher", "doctor", "engineer", "lawyer"]

    # Build variable names
    def V(cat, val): return f"{cat}:{val}"

    categories = {
        "Name": [V("Name", n) for n in Names],
        "Color": [V("Color", c) for c in Colors],
        "Phone": [V("Phone", p) for p in PhoneModels],
        "Occupation": [V("Occupation", o) for o in Occupations],
    }

    all_vars = categories["Name"] + categories["Color"] + categories["Phone"] + categories["Occupation"]

    # Map variable to its category
    var_to_cat = {}
    for cat, vars_list in categories.items():
        for var in vars_list:
            var_to_cat[var] = cat

    # Equality relations based on clues
    eq_pairs = [
        # 3. Samsung Galaxy S21 is the doctor
        (V("Phone", "samsung galaxy s21"), V("Occupation", "doctor")),
        # 4. Doctor loves blue
        (V("Occupation", "doctor"), V("Color", "blue")),
        # 6. Lawyer uses OnePlus 9
        (V("Occupation", "lawyer"), V("Phone", "oneplus 9")),
        # 10. Arnold is the engineer
        (V("Name", "Arnold"), V("Occupation", "engineer")),
        # 11. Alice loves yellow
        (V("Name", "Alice"), V("Color", "yellow")),
        # 12. Google Pixel 6 is Eric
        (V("Phone", "google pixel 6"), V("Name", "Eric")),
        # 13. Google Pixel 6 is the teacher
        (V("Phone", "google pixel 6"), V("Occupation", "teacher")),
    ]

    # Build undirected adjacency for equality graph
    eq_adj = defaultdict(set)
    for a, b in eq_pairs:
        eq_adj[a].add(b)
        eq_adj[b].add(a)

    def equal_group(var):
        # BFS to get all variables equal to var (transitively)
        seen = set()
        dq = deque([var])
        while dq:
            x = dq.popleft()
            if x in seen:
                continue
            seen.add(x)
            for y in eq_adj.get(x, []):
                if y not in seen:
                    dq.append(y)
        return seen

    # Helper to compute domain for a variable under current assignment
    def domain_of(var, assignment):
        dom = set(houses)

        cat = var_to_cat[var]

        # All-different within same category: remove used houses in same category
        for other in categories[cat]:
            if other in assignment and other != var:
                dom.discard(assignment[other])

        # Equality constraints: all variables in the same equality group must share house
        eg = equal_group(var)
        assigned_vals = {assignment[v] for v in eg if v in assignment}
        if len(assigned_vals) > 1:
            return set()  # conflict
        if len(assigned_vals) == 1:
            val = next(iter(assigned_vals))
            dom.intersection_update({val})

        # Specific unary constraints
        # 2. Bob is in the second house
        if var == V("Name", "Bob"):
            dom.intersection_update({2})

        # 5. Green not in fifth house
        if var == V("Color", "green"):
            dom.discard(5)

        # 7. Blue directly left of red -> blue in 1..4, red in 2..5
        if var == V("Color", "blue"):
            dom.intersection_update({1, 2, 3, 4})
            if V("Color", "red") in assignment:
                dom.intersection_update({assignment[V("Color", "red")] - 1})
        if var == V("Color", "red"):
            dom.intersection_update({2, 3, 4, 5})
            if V("Color", "blue") in assignment:
                dom.intersection_update({assignment[V("Color", "blue")] + 1})

        # 9. One house between Pixel 6 and Huawei P50
        pix = V("Phone", "google pixel 6")
        hua = V("Phone", "huawei p50")
        if var == pix and hua in assignment:
            h = assignment[hua]
            dom.intersection_update({h - 2, h + 2})
        if var == hua and pix in assignment:
            p = assignment[pix]
            dom.intersection_update({p - 2, p + 2})
        # Remove houses out of range after +/-2 ops
        dom = {d for d in dom if 1 <= d <= 5}

        # 1. Engineer right of lawyer
        if var == V("Occupation", "engineer") and V("Occupation", "lawyer") in assignment:
            L = assignment[V("Occupation", "lawyer")]
            dom.intersection_update({x for x in houses if x > L})
        if var == V("Occupation", "lawyer") and V("Occupation", "engineer") in assignment:
            E = assignment[V("Occupation", "engineer")]
            dom.intersection_update({x for x in houses if x < E})

        # 8. Lawyer right of Samsung Galaxy S21
        if var == V("Occupation", "lawyer") and V("Phone", "samsung galaxy s21") in assignment:
            S = assignment[V("Phone", "samsung galaxy s21")]
            dom.intersection_update({x for x in houses if x > S})
        if var == V("Phone", "samsung galaxy s21") and V("Occupation", "lawyer") in assignment:
            L = assignment[V("Occupation", "lawyer")]
            dom.intersection_update({x for x in houses if x < L})

        # 14. Red right of teacher
        if var == V("Color", "red") and V("Occupation", "teacher") in assignment:
            T = assignment[V("Occupation", "teacher")]
            dom.intersection_update({x for x in houses if x > T})
        if var == V("Occupation", "teacher") and V("Color", "red") in assignment:
            R = assignment[V("Color", "red")]
            dom.intersection_update({x for x in houses if x < R})

        return dom

    def is_consistent(assignment):
        # All-different within each category
        for cat, vars_list in categories.items():
            vals = [assignment[v] for v in vars_list if v in assignment]
            if len(vals) != len(set(vals)):
                return False

        # Equality constraints
        for a, b in eq_pairs:
            if a in assignment and b in assignment and assignment[a] != assignment[b]:
                return False

        # 2. Bob in second house
        if V("Name", "Bob") in assignment and assignment[V("Name", "Bob")] != 2:
            return False

        # 5. Green not in fifth
        if V("Color", "green") in assignment and assignment[V("Color", "green")] == 5:
            return False

        # 7. Blue immediately left of Red
        if V("Color", "blue") in assignment and V("Color", "red") in assignment:
            if assignment[V("Color", "blue")] + 1 != assignment[V("Color", "red")]:
                return False
        else:
            if V("Color", "blue") in assignment:
                if assignment[V("Color", "blue")] == 5:
                    return False
            if V("Color", "red") in assignment:
                if assignment[V("Color", "red")] == 1:
                    return False

        # 1. Engineer right of Lawyer
        if V("Occupation", "engineer") in assignment and V("Occupation", "lawyer") in assignment:
            if not (assignment[V("Occupation", "engineer")] > assignment[V("Occupation", "lawyer")]):
                return False

        # 8. Lawyer right of S21
        if V("Occupation", "lawyer") in assignment and V("Phone", "samsung galaxy s21") in assignment:
            if not (assignment[V("Occupation", "lawyer")] > assignment[V("Phone", "samsung galaxy s21")]):
                return False

        # 9. Pixel 6 and Huawei separated by one house between (diff of 2)
        if V("Phone", "google pixel 6") in assignment and V("Phone", "huawei p50") in assignment:
            if abs(assignment[V("Phone", "google pixel 6")] - assignment[V("Phone", "huawei p50")]) != 2:
                return False

        # 14. Red right of Teacher
        if V("Color", "red") in assignment and V("Occupation", "teacher") in assignment:
            if not (assignment[V("Color", "red")] > assignment[V("Occupation", "teacher")]):
                return False

        # Additional viability checks (prune impossible placements early)
        # Teacher cannot be 5 (since red must be to the right)
        if V("Occupation", "teacher") in assignment and assignment[V("Occupation", "teacher")] == 5:
            return False
        # Engineer cannot be 1 (must be right of lawyer)
        if V("Occupation", "engineer") in assignment and assignment[V("Occupation", "engineer")] == 1:
            return False
        # Lawyer cannot be 1 (must be right of S21 at least)
        if V("Occupation", "lawyer") in assignment and assignment[V("Occupation", "lawyer")] == 1:
            return False
        # S21 cannot be 5 (then lawyer couldn't be to the right)
        if V("Phone", "samsung galaxy s21") in assignment and assignment[V("Phone", "samsung galaxy s21")] == 5:
            return False

        return True

    # Propagate equalities: assign equal variables the same value
    def propagate_equalities(assignment):
        queue = deque([var for var in assignment.keys()])
        while queue:
            var = queue.popleft()
            val = assignment[var]
            for eqv in eq_adj.get(var, []):
                if eqv in assignment:
                    if assignment[eqv] != val:
                        return False
                else:
                    assignment[eqv] = val
                    queue.append(eqv)
        return True

    def forward_check(assignment):
        # If any unassigned variable has empty domain, fail
        for var in all_vars:
            if var not in assignment:
                dom = domain_of(var, assignment)
                if not dom:
                    return False
        return True

    def select_unassigned_variable(assignment):
        # Minimum Remaining Values heuristic
        best_var = None
        best_dom = None
        for var in all_vars:
            if var in assignment:
                continue
            dom = domain_of(var, assignment)
            if best_dom is None or len(dom) < len(best_dom) or (len(dom) == len(best_dom) and var < best_var):
                best_var = var
                best_dom = dom
            if best_dom is not None and len(best_dom) == 1:
                break
        return best_var, best_dom

    def backtrack(assignment):
        if len(assignment) == len(all_vars):
            return assignment

        var, dom = select_unassigned_variable(assignment)
        if dom is None or len(dom) == 0:
            return None

        for value in sorted(dom):
            new_assign = dict(assignment)
            new_assign[var] = value
            if not is_consistent(new_assign):
                continue
            if not propagate_equalities(new_assign):
                continue
            if not is_consistent(new_assign):
                continue
            if not forward_check(new_assign):
                continue
            result = backtrack(new_assign)
            if result is not None:
                return result
        return None

    # Initialize assignment with given constants
    init_assignment = {}
    init_assignment[V("Name", "Bob")] = 2

    # Propagate and start search
    if not propagate_equalities(init_assignment) or not is_consistent(init_assignment) or not forward_check(init_assignment):
        return None
    solution_assignment = backtrack(init_assignment)
    return solution_assignment

def build_output(assignment):
    # Prepare mapping from house to attributes
    Names = ["Bob", "Eric", "Arnold", "Alice", "Peter"]
    Colors = ["blue", "green", "white", "yellow", "red"]
    PhoneModels = ["huawei p50", "samsung galaxy s21", "oneplus 9", "iphone 13", "google pixel 6"]
    Occupations = ["artist", "teacher", "doctor", "engineer", "lawyer"]

    def V(cat, val): return f"{cat}:{val}"

    name_by_house = {}
    color_by_house = {}
    phone_by_house = {}
    occ_by_house = {}

    for n in Names:
        name_by_house[assignment[V("Name", n)]] = n
    for c in Colors:
        color_by_house[assignment[V("Color", c)]] = c
    for p in PhoneModels:
        phone_by_house[assignment[V("Phone", p)]] = p
    for o in Occupations:
        occ_by_house[assignment[V("Occupation", o)]] = o

    rows = []
    for h in range(1, 6):
        rows.append([str(h), name_by_house[h], color_by_house[h], phone_by_house[h], occ_by_house[h]])

    output = {
        "solution": {
            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
            "rows": rows
        }
    }
    return output

def main():
    assignment = solve_puzzle()
    if assignment is None:
        print(json.dumps({"solution": {"header": ["House", "Name", "Color", "PhoneModel", "Occupation"], "rows": []}}))
        return
    output = build_output(assignment)
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()