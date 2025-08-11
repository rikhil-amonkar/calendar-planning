import json

# Define the puzzle categories and values
categories = {
    "name": ["Eric", "Peter", "Arnold"],
    "favorite drink": ["milk", "water", "tea"],
    "vacation": ["mountain", "city", "beach"],
    "house": ["colonial", "victorian", "ranch"],
    "animals": ["cat", "bird", "horse"],
    "birthday month": ["jan", "sept", "april"],
}

positions = [1, 2, 3]

# Constraints representation:
# - type: 'same', 'leftof', 'immediate_leftof'
# - a, b: each is a tuple (category, value)
constraints = []

def same(a, b):
    constraints.append({"type": "same", "a": a, "b": b})

def leftof(a, b):
    constraints.append({"type": "leftof", "a": a, "b": b})

def immediate_leftof(a, b):
    constraints.append({"type": "immediate_leftof", "a": a, "b": b})

# Encode the clues:
# 1. colonial left of milk
leftof(("house", "colonial"), ("favorite drink", "milk"))

# 2. city directly left of victorian
immediate_leftof(("vacation", "city"), ("house", "victorian"))

# 3. jan directly left of cat
immediate_leftof(("birthday month", "jan"), ("animals", "cat"))

# 4. water == mountain
same(("favorite drink", "water"), ("vacation", "mountain"))

# 5. horse == Peter
same(("animals", "horse"), ("name", "Peter"))

# 6. victorian right of beach  => beach left of victorian
leftof(("vacation", "beach"), ("house", "victorian"))

# 7. Peter == city
same(("name", "Peter"), ("vacation", "city"))

# 8. mountain == april
same(("vacation", "mountain"), ("birthday month", "april"))

# 9. Eric == water
same(("name", "Eric"), ("favorite drink", "water"))

# Prepare all pairs
all_pairs = []
for cat, vals in categories.items():
    for v in vals:
        all_pairs.append((cat, v))

# Map pair -> constraints it's involved in (for degree heuristic)
pair_degree = {p: 0 for p in all_pairs}
for c in constraints:
    pair_degree[c["a"]] += 1
    pair_degree[c["b"]] += 1

def available_positions(cat, used_positions):
    return [p for p in positions if p not in used_positions[cat]]

def check_constraints(assignments, used_positions):
    # For each constraint, verify it's satisfied or still satisfiable
    for c in constraints:
        typ = c["type"]
        a = c["a"]
        b = c["b"]
        pos_a = assignments.get(a)
        pos_b = assignments.get(b)

        if typ == "same":
            if pos_a is not None and pos_b is not None:
                if pos_a != pos_b:
                    return False
            elif pos_a is not None and pos_b is None:
                # Ensure pos_a still available in b's category
                cat_b = b[0]
                if pos_a in used_positions[cat_b]:
                    return False
            elif pos_b is not None and pos_a is None:
                cat_a = a[0]
                if pos_b in used_positions[cat_a]:
                    return False

        elif typ == "leftof":
            if pos_a is not None and pos_b is not None:
                if not (pos_a < pos_b):
                    return False
            elif pos_a is not None and pos_b is None:
                # Need some available position for b greater than pos_a
                cat_b = b[0]
                poss_b = [p for p in available_positions(cat_b, used_positions) if p > pos_a]
                if not poss_b:
                    return False
            elif pos_b is not None and pos_a is None:
                # Need some available position for a less than pos_b
                cat_a = a[0]
                poss_a = [p for p in available_positions(cat_a, used_positions) if p < pos_b]
                if not poss_a:
                    return False

        elif typ == "immediate_leftof":
            if pos_a is not None and pos_b is not None:
                if pos_b != pos_a + 1:
                    return False
            elif pos_a is not None and pos_b is None:
                # pos_b must be pos_a + 1 and available
                if pos_a >= 3:
                    return False
                needed = pos_a + 1
                cat_b = b[0]
                if needed in used_positions[cat_b]:
                    return False
            elif pos_b is not None and pos_a is None:
                if pos_b <= 1:
                    return False
                needed = pos_b - 1
                cat_a = a[0]
                if needed in used_positions[cat_a]:
                    return False
    return True

def domain_for_pair(pair, assignments, used_positions):
    if pair in assignments:
        return [assignments[pair]]
    cat = pair[0]
    dom = []
    for pos in available_positions(cat, used_positions):
        # Try assigning and test constraints
        assignments[pair] = pos
        used_positions[cat].add(pos)
        ok = check_constraints(assignments, used_positions)
        used_positions[cat].remove(pos)
        del assignments[pair]
        if ok:
            dom.append(pos)
    return dom

def select_unassigned_pair(assignments, used_positions):
    # MRV: choose pair with smallest domain
    unassigned = [p for p in all_pairs if p not in assignments]
    # Compute domains
    domains = {p: domain_for_pair(p, assignments, used_positions) for p in unassigned}
    # If any domain is empty, return that immediately to prune
    # Otherwise choose by smallest domain size, tie-breaker by highest degree
    best = None
    best_dom = None
    for p in unassigned:
        d = domains[p]
        if len(d) == 0:
            return p, d  # Force immediate failure
        if best is None or len(d) < len(best_dom) or (len(d) == len(best_dom) and pair_degree[p] > pair_degree[best]):
            best = p
            best_dom = d
    return best, best_dom

def backtrack(assignments, used_positions):
    if len(assignments) == len(all_pairs):
        if check_constraints(assignments, used_positions):
            return assignments
        return None

    pair, dom = select_unassigned_pair(assignments, used_positions)
    if dom is None or len(dom) == 0:
        return None

    cat = pair[0]
    # Try values in domain
    for pos in dom:
        assignments[pair] = pos
        used_positions[cat].add(pos)
        if check_constraints(assignments, used_positions):
            res = backtrack(assignments, used_positions)
            if res is not None:
                return res
        used_positions[cat].remove(pos)
        del assignments[pair]
    return None

def solve_puzzle():
    assignments = {}
    used_positions = {cat: set() for cat in categories}
    solution = backtrack(assignments, used_positions)
    if solution is None:
        raise RuntimeError("No solution found")
    return solution

def to_rows(assignments):
    header = ["House", "name", "favorite drink", "vacation", "house", "animals", "birthday month"]
    rows = []
    # Build reverse lookup: for each category, pos -> value
    pos_to_value = {cat: {pos: None for pos in positions} for cat in categories}
    for (cat, val), pos in assignments.items():
        pos_to_value[cat][pos] = val
    for pos in positions:
        row = [str(pos)]
        row.append(pos_to_value["name"][pos])
        row.append(pos_to_value["favorite drink"][pos])
        row.append(pos_to_value["vacation"][pos])
        row.append(pos_to_value["house"][pos])
        row.append(pos_to_value["animals"][pos])
        row.append(pos_to_value["birthday month"][pos])
        rows.append(row)
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    assignments = solve_puzzle()
    result = to_rows(assignments)
    print(json.dumps(result, ensure_ascii=False))