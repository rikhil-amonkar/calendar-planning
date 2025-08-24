import json
from copy import deepcopy

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]

    categories = {
        "Name": ["Arnold", "Carol", "Eric", "Bob", "Alice", "Peter"],
        "Birthday": ["feb", "mar", "sept", "jan", "may", "april"],
        "Food": ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"],
        "Height": ["very short", "average", "super tall", "short", "very tall", "tall"],
        "CarModel": ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]
    }

    # Map item -> category
    item_to_cat = {}
    for cat, items in categories.items():
        for it in items:
            item_to_cat[it] = cat

    items = sum(categories.values(), [])

    # Domains: each item can be in any house initially
    domains = {it: set(houses) for it in items}

    # Apply initial fixed placements and exclusions
    # 19. The person who is very short is in the fourth house.
    domains["very short"] = {4}

    # 2. The person who owns a Ford F-150 is in the fifth house.
    domains["ford f150"] = {5}

    # 6. The person who owns a BMW 3 Series is not in the third house.
    if 3 in domains["bmw 3 series"]:
        domains["bmw 3 series"].remove(3)

    # 14. The person who loves the stew is not in the third house.
    if 3 in domains["stew"]:
        domains["stew"].remove(3)

    # Constraints
    # Equalities (same house)
    EQ = [
        ("honda civic", "short"),     # 1
        ("mar", "short"),             # 20
        ("Eric", "jan"),              # 22
        ("Carol", "tesla model 3"),   # 21
        ("very tall", "toyota camry"),# 12
        ("Bob", "tall"),              # 17
    ]

    # Left of constraints (strictly left)
    LO = [
        ("stir fry", "Eric"),         # 3
        ("may", "Carol"),             # 4
        ("very short", "april"),      # 5
        ("tesla model 3", "tall"),    # 11
        ("Carol", "Bob"),             # derived from 11 and 17 and 21
        ("Alice", "may"),             # 18
    ]

    # Directly left of constraints
    ADJLEFT = [
        ("soup", "Eric"),             # 8
        ("Peter", "pizza"),           # 13
        ("Alice", "bmw 3 series"),    # 10
    ]

    # Adjacent (either side, distance 1)
    ADJACENT = [
        ("spaghetti", "may"),         # 9
    ]

    # Distance exactly 2 (one house between, order not specified)
    DIFF2 = [
        ("sept", "very short"),       # 15
        ("mar", "super tall"),        # 16
    ]

    # Distance exactly 3 (two houses between, order not specified)
    DIFF3 = [
        ("stir fry", "pizza"),        # 7
    ]

    # Helper functions
    def category_of(item):
        return item_to_cat[item]

    def clone_domains(d):
        return {k: set(v) for k, v in d.items()}

    # Consistency checks using current assignments and domains
    def is_consistent(assignments, domains):
        # Uniqueness within each category
        for cat, its in categories.items():
            seen = {}
            for it in its:
                if it in assignments:
                    pos = assignments[it]
                    if pos in seen:
                        return False
                    seen[pos] = it

        # Equality constraints
        for a, b in EQ:
            pa = assignments.get(a)
            pb = assignments.get(b)
            if pa is not None and pb is not None:
                if pa != pb:
                    return False
            elif pa is not None and pb is None:
                if pa not in domains[b]:
                    return False
            elif pa is None and pb is not None:
                if pb not in domains[a]:
                    return False
            else:
                # Both unassigned, domains must have some overlap
                if domains[a].isdisjoint(domains[b]):
                    return False

        # Left-of constraints
        for a, b in LO:
            pa = assignments.get(a)
            pb = assignments.get(b)
            if pa is not None and pb is not None:
                if not (pa < pb):
                    return False
            elif pa is not None and pb is None:
                # b must have some domain position > pa
                if not any(x > pa for x in domains[b]):
                    return False
            elif pa is None and pb is not None:
                if not any(x < pb for x in domains[a]):
                    return False
            else:
                # both unassigned: can skip or do a coarse check
                pass

        # Directly left-of constraints
        for a, b in ADJLEFT:
            pa = assignments.get(a)
            pb = assignments.get(b)
            if pa is not None and pb is not None:
                if pb - pa != 1:
                    return False
            elif pa is not None and pb is None:
                # b must be pa+1
                if pa == 6 or (pa + 1) not in domains[b]:
                    return False
            elif pa is None and pb is not None:
                if pb == 1 or (pb - 1) not in domains[a]:
                    return False
            else:
                pass

        # Adjacent (abs diff 1)
        for a, b in ADJACENT:
            pa = assignments.get(a)
            pb = assignments.get(b)
            if pa is not None and pb is not None:
                if abs(pb - pa) != 1:
                    return False
            elif pa is not None and pb is None:
                opts = set()
                if pa - 1 >= 1:
                    opts.add(pa - 1)
                if pa + 1 <= 6:
                    opts.add(pa + 1)
                if not (domains[b] & opts):
                    return False
            elif pa is None and pb is not None:
                opts = set()
                if pb - 1 >= 1:
                    opts.add(pb - 1)
                if pb + 1 <= 6:
                    opts.add(pb + 1)
                if not (domains[a] & opts):
                    return False
            else:
                pass

        # Distance 2
        for a, b in DIFF2:
            pa = assignments.get(a)
            pb = assignments.get(b)
            if pa is not None and pb is not None:
                if abs(pb - pa) != 2:
                    return False
            elif pa is not None and pb is None:
                opts = set()
                if pa - 2 >= 1:
                    opts.add(pa - 2)
                if pa + 2 <= 6:
                    opts.add(pa + 2)
                if not (domains[b] & opts):
                    return False
            elif pa is None and pb is not None:
                opts = set()
                if pb - 2 >= 1:
                    opts.add(pb - 2)
                if pb + 2 <= 6:
                    opts.add(pb + 2)
                if not (domains[a] & opts):
                    return False
            else:
                pass

        # Distance 3
        for a, b in DIFF3:
            pa = assignments.get(a)
            pb = assignments.get(b)
            if pa is not None and pb is not None:
                if abs(pb - pa) != 3:
                    return False
            elif pa is not None and pb is None:
                opts = set()
                if pa - 3 >= 1:
                    opts.add(pa - 3)
                if pa + 3 <= 6:
                    opts.add(pa + 3)
                if not (domains[b] & opts):
                    return False
            elif pa is None and pb is not None:
                opts = set()
                if pb - 3 >= 1:
                    opts.add(pb - 3)
                if pb + 3 <= 6:
                    opts.add(pb + 3)
                if not (domains[a] & opts):
                    return False
            else:
                pass

        # Additional derived constraints:
        # April must be to the right of very short (already LO), and since very short at 4,
        # April must be in {5,6}. Ensure domains reflect possibility
        if "april" not in assignments:
            if not any(x > 4 for x in domains["april"]):
                return False
        else:
            if assignments["april"] <= 4:
                return False

        return True

    # Assign and propagate only basic constraints: category uniqueness and equalities
    def assign(item, pos, assignments, domains):
        new_assign = dict(assignments)
        new_domains = clone_domains(domains)

        # Assign item
        new_assign[item] = pos
        new_domains[item] = {pos}

        # Category uniqueness: remove pos from other items in same category
        cat = category_of(item)
        for other in categories[cat]:
            if other != item and other not in new_assign:
                if pos in new_domains[other]:
                    new_domains[other].remove(pos)
                    if not new_domains[other]:
                        return None, None

        # Equality propagation
        for a, b in EQ:
            if a == item:
                # set b to same pos
                if b in new_assign and new_assign[b] != pos:
                    return None, None
                new_domains[b] = {pos}
            elif b == item:
                if a in new_assign and new_assign[a] != pos:
                    return None, None
                new_domains[a] = {pos}

        return new_assign, new_domains

    def choose_var(assignments, domains):
        unassigned = [it for it in items if it not in assignments]
        # Minimum Remaining Values (domain size), tie-break by category or name for determinism
        unassigned.sort(key=lambda it: (len(domains[it]), item_to_cat[it], it))
        return unassigned[0] if unassigned else None

    solution = {}

    def backtrack(assignments, domains):
        nonlocal solution
        if len(assignments) == len(items):
            if is_consistent(assignments, domains):
                solution = assignments
                return True
            return False

        if not is_consistent(assignments, domains):
            return False

        var = choose_var(assignments, domains)
        if var is None:
            return False

        # Try values in domain
        for val in sorted(domains[var]):
            # Skip if category conflict (redundant but safe)
            cat = category_of(var)
            conflict = False
            for it in categories[cat]:
                if it in assignments and assignments[it] == val and it != var:
                    conflict = True
                    break
            if conflict:
                continue

            new_assign, new_domains = assign(var, val, assignments, domains)
            if new_assign is None:
                continue

            if is_consistent(new_assign, new_domains):
                if backtrack(new_assign, new_domains):
                    return True
        return False

    # Start search
    backtrack({}, domains)

    if not solution:
        raise RuntimeError("No solution found")

    # Build output rows
    # Map house -> attributes
    rows = []
    for h in houses:
        # Find each category item in this house
        name = next(n for n in categories["Name"] if solution[n] == h)
        bday = next(b for b in categories["Birthday"] if solution[b] == h)
        food = next(f for f in categories["Food"] if solution[f] == h)
        height = next(he for he in categories["Height"] if solution[he] == h)
        car = next(c for c in categories["CarModel"] if solution[c] == h)
        rows.append([str(h), name, bday, food, height, car])

    return {
        "solution": {
            "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))