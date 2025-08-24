import json
from copy import deepcopy

def solve_puzzle():
    # Houses
    houses = [1, 2]

    # Categories and their possible values
    categories = ["Name", "Education", "Height", "Food", "Drink"]
    values = {
        "Name": ["Arnold", "Eric"],
        "Education": ["associate", "high school"],
        "Height": ["short", "very short"],
        "Food": ["grilled cheese", "pizza"],
        "Drink": ["tea", "water"],
    }

    # Equivalence constraints: (cat1, val1) <-> (cat2, val2)
    equivalences = [
        ("Height", "very short", "Food", "pizza"),
        ("Education", "high school", "Food", "pizza"),
        ("Drink", "tea", "Food", "grilled cheese"),
        ("Name", "Arnold", "Food", "pizza"),
    ]

    # House-specific constraints: house -> {category: value}
    house_constraints = {
        2: {"Food": "grilled cheese"}
    }

    # Initialize assignments: assignments[house][category] = value or None
    assignments = {h: {cat: None for cat in categories} for h in houses}

    # Used values per category to ensure uniqueness across houses
    used_values = {cat: set() for cat in categories}

    # Apply direct house constraints initially (if any)
    for h, consts in house_constraints.items():
        for cat, val in consts.items():
            assignments[h][cat] = val
            used_values[cat].add(val)

    def domains_of(h, cat, current_assignments, current_used):
        # Start with available values not already used for this category
        dom = [v for v in values[cat] if v not in current_used[cat]]

        # Respect direct house constraints
        if h in house_constraints and cat in house_constraints[h]:
            forced = house_constraints[h][cat]
            dom = [v for v in dom if v == forced]

        # Apply equivalence constraints
        for (c1, v1, c2, v2) in equivalences:
            # If this variable is c1, relate it to c2
            if cat == c1:
                other_val = current_assignments[h][c2]
                if other_val is not None:
                    if other_val == v2:
                        # Must be v1
                        dom = [v for v in dom if v == v1]
                    else:
                        # Cannot be v1
                        dom = [v for v in dom if v != v1]
            # If this variable is c2, relate it to c1
            if cat == c2:
                other_val = current_assignments[h][c1]
                if other_val is not None:
                    if other_val == v1:
                        dom = [v for v in dom if v == v2]
                    else:
                        dom = [v for v in dom if v != v2]

        return dom

    def is_consistent(h, cat, val, current_assignments, current_used):
        # Uniqueness check
        if val in current_used[cat]:
            return False

        # Check house-specific constraint
        if h in house_constraints and cat in house_constraints[h]:
            if val != house_constraints[h][cat]:
                return False

        # Check equivalences for immediate contradictions
        for (c1, v1, c2, v2) in equivalences:
            if cat == c1 and val == v1:
                other = current_assignments[h][c2]
                if other is not None and other != v2:
                    return False
            if cat == c2 and val == v2:
                other = current_assignments[h][c1]
                if other is not None and other != v1:
                    return False
            if cat == c1 and val != v1:
                other = current_assignments[h][c2]
                if other == v2:
                    return False
            if cat == c2 and val != v2:
                other = current_assignments[h][c1]
                if other == v1:
                    return False

        return True

    def all_assigned(current_assignments):
        for h in houses:
            for cat in categories:
                if current_assignments[h][cat] is None:
                    return False
        return True

    def select_unassigned_var(current_assignments, current_used):
        # Use MRV heuristic: select (house, category) with smallest domain
        best = None
        best_domain = None
        for h in houses:
            for cat in categories:
                if current_assignments[h][cat] is None:
                    dom = domains_of(h, cat, current_assignments, current_used)
                    if len(dom) == 0:
                        return (h, cat, [])  # immediate failure
                    if best is None or len(dom) < len(best_domain):
                        best = (h, cat)
                        best_domain = dom
                        if len(best_domain) == 1:
                            return (best[0], best[1], best_domain)
        if best is None:
            return None
        return (best[0], best[1], best_domain)

    def backtrack(current_assignments, current_used):
        if all_assigned(current_assignments):
            return current_assignments

        sel = select_unassigned_var(current_assignments, current_used)
        if sel is None:
            return None
        h, cat, domain = sel
        if len(domain) == 0:
            return None

        for val in domain:
            if not is_consistent(h, cat, val, current_assignments, current_used):
                continue

            # Assign
            next_assignments = deepcopy(current_assignments)
            next_used = deepcopy(current_used)
            next_assignments[h][cat] = val
            next_used[cat].add(val)

            # Forward check: ensure no remaining variable has empty domain
            empty_domain_found = False
            for hh in houses:
                for cc in categories:
                    if next_assignments[hh][cc] is None:
                        dom_check = domains_of(hh, cc, next_assignments, next_used)
                        if len(dom_check) == 0:
                            empty_domain_found = True
                            break
                if empty_domain_found:
                    break
            if empty_domain_found:
                continue

            result = backtrack(next_assignments, next_used)
            if result is not None:
                return result

        return None

    solution_assignments = backtrack(assignments, used_values)
    if solution_assignments is None:
        raise ValueError("No solution found for the puzzle.")

    # Build JSON output
    header = ["House", "Name", "Education", "Height", "Food", "Drink"]
    rows = []
    for h in houses:
        row = [
            str(h),
            solution_assignments[h]["Name"],
            solution_assignments[h]["Education"],
            solution_assignments[h]["Height"],
            solution_assignments[h]["Food"],
            solution_assignments[h]["Drink"],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))