import json
from collections import deque
from copy import deepcopy

def solve():
    # Houses indexed from 1..N
    houses = [1, 2]
    N = len(houses)

    # Attributes and their possible values
    attributes = ["Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"]
    values = {
        "Name": ["Arnold", "Eric"],
        "Occupation": ["engineer", "doctor"],
        "Birthday": ["april", "sept"],
        "HouseStyle": ["victorian", "colonial"],
        "Height": ["very short", "short"],
        "Cigar": ["pall mall", "prince"],
    }

    # Helper to get neighbors (adjacent houses)
    def neighbors(h):
        nb = []
        if h - 1 >= 1:
            nb.append(h - 1)
        if h + 1 <= N:
            nb.append(h + 1)
        return nb

    # Initialize domains: for each (house, attribute) variable, a set of possible values
    domains = {}
    for h in houses:
        for attr in attributes:
            domains[(h, attr)] = set(values[attr])

    # Equality links (same person constraints): (attrA,valA) <-> (attrB,valB)
    # These are bidirectional equivalences: if a house has (attrA=valA), it must also have (attrB=valB), and vice versa.
    eq_pairs = [
        (("Occupation", "engineer"), ("HouseStyle", "colonial")),
        (("HouseStyle", "colonial"), ("Occupation", "engineer")),
        (("Occupation", "engineer"), ("Height", "very short")),
        (("Height", "very short"), ("Occupation", "engineer")),
        (("Occupation", "engineer"), ("Name", "Eric")),
        (("Name", "Eric"), ("Occupation", "engineer")),
        (("Height", "short"), ("Cigar", "pall mall")),
        (("Cigar", "pall mall"), ("Height", "short")),
    ]

    # Next-to (adjacency) constraints: (attrA,valA) is next to (attrB,valB)
    # We'll include both directions for ease of propagation.
    nextto_pairs = [
        (("Birthday", "april"), ("Occupation", "doctor")),
        (("Occupation", "doctor"), ("Birthday", "april")),
    ]

    # Utility functions for CSP operations
    def is_assigned(var):
        return len(domains[var]) == 1

    def get_value(var):
        s = domains[var]
        return next(iter(s)) if len(s) == 1 else None

    def enqueue_if_single(queue, var):
        if len(domains[var]) == 1:
            queue.append(var)

    def eliminate(var, val, queue):
        if val not in domains[var]:
            return True  # already eliminated
        domains[var].remove(val)
        if len(domains[var]) == 0:
            return False  # contradiction
        if len(domains[var]) == 1:
            queue.append(var)
        return True

    def assign(var, val, queue):
        # Assign var to val by eliminating all other values
        if val not in domains[var]:
            return False
        other_vals = set(domains[var]) - {val}
        for ov in list(other_vals):
            ok = eliminate(var, ov, queue)
            if not ok:
                return False
        return True

    def propagate(queue):
        while queue:
            var = queue.popleft()
            h, attr = var
            if len(domains[var]) != 1:
                continue
            val = get_value(var)

            # All-different per attribute across houses:
            for h2 in houses:
                if h2 != h:
                    var2 = (h2, attr)
                    if val in domains[var2]:
                        if not eliminate(var2, val, queue):
                            return False

            # Equality links propagation
            for (a1, v1), (a2, v2) in eq_pairs:
                if attr == a1 and val == v1:
                    var2 = (h, a2)
                    if not assign(var2, v2, queue):
                        return False

            # Next-to constraints propagation
            def enforce_next_to(house_from, target_attr, target_val):
                # Not same house:
                if not eliminate((house_from, target_attr), target_val, queue):
                    return False
                # Remove target_val from non-neighbor houses:
                nbs = set(neighbors(house_from))
                for h_other in houses:
                    if h_other != house_from and h_other not in nbs:
                        if not eliminate((h_other, target_attr), target_val, queue):
                            return False
                # Ensure at least one neighbor can take target_val:
                candidates = [hn for hn in nbs if target_val in domains[(hn, target_attr)]]
                if len(candidates) == 0:
                    return False
                # If only one neighbor can take it, assign it there:
                if len(candidates) == 1:
                    if not assign((candidates[0], target_attr), target_val, queue):
                        return False
                return True

            for (a1, v1), (a2, v2) in nextto_pairs:
                if attr == a1 and val == v1:
                    if not enforce_next_to(h, a2, v2):
                        return False

        return True

    def is_solved(dom):
        return all(len(dom[var]) == 1 for var in dom)

    def select_unassigned_variable(dom):
        # Minimum Remaining Values heuristic
        unassigned = [var for var in dom if len(dom[var]) > 1]
        if not unassigned:
            return None
        return min(unassigned, key=lambda v: len(dom[v]))

    def backtrack(dom):
        if is_solved(dom):
            return dom
        var = select_unassigned_variable(dom)
        if var is None:
            return dom
        h, attr = var
        for val in sorted(dom[var]):
            dom_copy = deepcopy(dom)
            q = deque()
            if assign(var, val, q):
                if propagate(q):
                    result = backtrack(dom_copy)
                    if result is not None and is_solved(result):
                        return result
            # restore dom for next iteration
            dom = dom_copy
        return None

    # Apply initial direct constraints from clues:

    # 1. The person who is an engineer is in the first house.
    q = deque()
    if not assign((1, "Occupation"), "engineer", q):
        return None

    # Propagate initial constraints (equality links and all-different will push doctor to house 2, etc.)
    if not propagate(q):
        return None

    # 6. The person who is an engineer is Eric.
    # Already captured via equality link in eq_pairs.

    # 3. Colonial house is the engineer's house.
    # Already captured via equality link in eq_pairs.

    # 4. Very short is the engineer.
    # Already captured via equality link in eq_pairs.

    # 5. Short is Pall Mall.
    # Already captured via equality link in eq_pairs.

    # 2. April and Doctor are next to each other.
    # Already captured in nextto_pairs; propagation will handle when either is assigned.

    # Now solve via backtracking (though propagation may already solve completely)
    solution_domains = backtrack(domains)
    if solution_domains is None:
        raise RuntimeError("No solution found")

    # Build output JSON
    header = ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"]
    rows = []
    for h in houses:
        row = [
            str(h),
            get_value((h, "Name")),
            get_value((h, "Occupation")),
            get_value((h, "Birthday")),
            get_value((h, "HouseStyle")),
            get_value((h, "Height")),
            get_value((h, "Cigar")),
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    solve()