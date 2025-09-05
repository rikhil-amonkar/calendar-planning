import json
from copy import deepcopy

def zebra_puzzle_solver():
    houses = [1, 2, 3, 4, 5, 6]

    categories = {
        "Name": ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"],
        "PhoneModel": ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"],
        "Cigar": ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"],
        "Flower": ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"],
        "Color": ["yellow", "red", "green", "blue", "white", "purple"],
        "FavoriteSport": ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"],
    }

    # Map each value label to its category
    label_to_category = {}
    for cat, vals in categories.items():
        for v in vals:
            label_to_category[v] = cat

    # Initialize domains: each label can be in any house initially
    domains = {label: set(houses) for label in label_to_category.keys()}

    # Constraints storage
    constraints = []

    def add_eq(a, b):
        constraints.append(("eq", a, b))

    def add_eq_val(a, val):
        constraints.append(("eq_val", a, val))

    def add_lt(a, b):
        constraints.append(("lt", a, b))  # pos(a) < pos(b)

    def add_adj_left(a, b):
        constraints.append(("adj_left", a, b))  # pos(a) + 1 == pos(b)

    def add_next_to(a, b):
        constraints.append(("next_to", a, b))  # |pos(a) - pos(b)| == 1

    def add_distance(a, b, d):
        constraints.append(("distance", a, b, d))  # |pos(a) - pos(b)| == d

    # Add puzzle constraints:

    # 1. The person who uses a OnePlus 9 is in the second house.
    add_eq_val("oneplus 9", 2)

    # 2. The person who uses a Xiaomi Mi 11 is somewhere to the left of the person who uses a Huawei P50.
    add_lt("xiaomi mi 11", "huawei p50")

    # 3. Carol is the person who loves a carnations arrangement.
    add_eq("Carol", "carnations")

    # 4. The person who loves purple is directly left of the person partial to Pall Mall.
    add_adj_left("purple", "pall mall")

    # 5. The person whose favorite color is green is the person who smokes Blue Master.
    add_eq("green", "blue master")

    # 6. The person who loves yellow and the person who loves blue are next to each other.
    add_next_to("yellow", "blue")

    # 7. Eric is somewhere to the right of the person who uses a Samsung Galaxy S21.
    add_lt("samsung galaxy s21", "Eric")

    # 8. There are two houses between Carol and the person who loves a bouquet of daffodils.
    add_distance("Carol", "daffodils", 3)

    # 9. The Prince smoker is the person who loves basketball.
    add_eq("prince", "basketball")

    # 10. The Dunhill smoker is the person who loves volleyball.
    add_eq("dunhill", "volleyball")

    # 11. The person who loves swimming is the person who uses a Google Pixel 6.
    add_eq("swimming", "google pixel 6")

    # 12. The person who uses a Huawei P50 is directly left of the person who loves white.
    add_adj_left("huawei p50", "white")

    # 13. The person who uses a OnePlus 9 and the person who loves the rose bouquet are next to each other.
    add_next_to("oneplus 9", "roses")

    # 14. The person who loves the boquet of iris is somewhere to the left of Eric.
    add_lt("iris", "Eric")

    # 15. The Dunhill smoker is Peter.
    add_eq("dunhill", "Peter")

    # 16. The person who loves blue is Peter.
    add_eq("blue", "Peter")

    # 17. The person who loves the vase of tulips is Bob.
    add_eq("tulips", "Bob")

    # 18. Alice is in the first house.
    add_eq_val("Alice", 1)

    # 19. The person who loves baseball is directly left of the person who smokes Blue Master.
    add_adj_left("baseball", "blue master")

    # 20. The person who uses a Google Pixel 6 is somewhere to the right of the person who smokes many unique blends.
    add_lt("blends", "google pixel 6")

    # 21. The person who loves soccer is Carol.
    add_eq("soccer", "Carol")

    # 22. The person who loves a carnations arrangement is directly left of the person who smokes many unique blends.
    add_adj_left("carnations", "blends")

    # 23. Eric is the person who smokes many unique blends.
    add_eq("Eric", "blends")

    # 24. The person who loves volleyball is the person who uses an iPhone 13.
    add_eq("volleyball", "iphone 13")

    # Propagation functions
    def propagate(dom):
        changed = True
        while changed:
            changed = False

            # Apply simple eq_val constraints directly
            for con in constraints:
                if con[0] == "eq_val":
                    _, a, val = con
                    if val not in dom[a]:
                        return False, dom
                    if dom[a] != {val}:
                        dom[a] = {val}
                        changed = True

            # Equality constraints A == B
            for con in constraints:
                if con[0] == "eq":
                    _, a, b = con
                    inter = dom[a] & dom[b]
                    if not inter:
                        return False, dom
                    if inter != dom[a]:
                        dom[a] = set(inter)
                        changed = True
                    if inter != dom[b]:
                        dom[b] = set(inter)
                        changed = True

            # Less-than constraints A < B
            for con in constraints:
                if con[0] == "lt":
                    _, a, b = con
                    da, db = dom[a], dom[b]
                    new_da = set(x for x in da if any(x < y for y in db))
                    new_db = set(y for y in db if any(x < y for x in da))
                    if not new_da or not new_db:
                        return False, dom
                    if new_da != da:
                        dom[a] = new_da
                        changed = True
                    if new_db != db:
                        dom[b] = new_db
                        changed = True

            # Adjacent left: A = B - 1
            for con in constraints:
                if con[0] == "adj_left":
                    _, a, b = con
                    da, db = dom[a], dom[b]
                    new_da = set(x for x in da if (x + 1) in db)
                    new_db = set(y for y in db if (y - 1) in da)
                    if not new_da or not new_db:
                        return False, dom
                    if new_da != da:
                        dom[a] = new_da
                        changed = True
                    if new_db != db:
                        dom[b] = new_db
                        changed = True

            # Next to: |A - B| == 1
            for con in constraints:
                if con[0] == "next_to":
                    _, a, b = con
                    da, db = dom[a], dom[b]
                    new_da = set(x for x in da if (x - 1) in db or (x + 1) in db)
                    new_db = set(y for y in db if (y - 1) in da or (y + 1) in da)
                    if not new_da or not new_db:
                        return False, dom
                    if new_da != da:
                        dom[a] = new_da
                        changed = True
                    if new_db != db:
                        dom[b] = new_db
                        changed = True

            # Distance: |A - B| == d
            for con in constraints:
                if con[0] == "distance":
                    _, a, b, d = con
                    da, db = dom[a], dom[b]
                    new_da = set(x for x in da if (x - d) in db or (x + d) in db)
                    new_db = set(y for y in db if (y - d) in da or (y + d) in da)
                    if not new_da or not new_db:
                        return False, dom
                    if new_da != da:
                        dom[a] = new_da
                        changed = True
                    if new_db != db:
                        dom[b] = new_db
                        changed = True

            # All-different per category (forward-checking, hidden singles, and duplicate-singleton check)
            for cat, vals in categories.items():
                # Duplicate-singleton detection (two values in same category assigned to same position)
                singleton_pos_counts = {}
                for v in vals:
                    if len(dom[v]) == 1:
                        p = next(iter(dom[v]))
                        singleton_pos_counts[p] = singleton_pos_counts.get(p, 0) + 1
                if any(c > 1 for c in singleton_pos_counts.values()):
                    return False, dom

                # Remove used positions (singletons) from others in same category
                assigned_positions = set()
                for v in vals:
                    if len(dom[v]) == 1:
                        assigned_positions |= dom[v]
                for v in vals:
                    if len(dom[v]) > 1:
                        new_domain = dom[v] - assigned_positions
                        if not new_domain:
                            return False, dom
                        if new_domain != dom[v]:
                            dom[v] = new_domain
                            changed = True

                # Hidden single: if a position is only possible for one value in a category, assign it
                pos_to_vals = {p: [] for p in houses}
                for v in vals:
                    for p in dom[v]:
                        pos_to_vals[p].append(v)
                for p, vs in pos_to_vals.items():
                    if len(vs) == 1:
                        v = vs[0]
                        if dom[v] != {p}:
                            dom[v] = {p}
                            changed = True

        return True, dom

    def is_solved(dom):
        # Every variable has a singleton domain and each category is a permutation of houses
        if not all(len(dom[v]) == 1 for v in dom):
            return False
        for cat, vals in categories.items():
            positions = [next(iter(dom[v])) for v in vals]
            if set(positions) != set(houses):
                return False
        return True

    def select_unassigned_variable(dom):
        # Choose the variable with the smallest domain > 1
        candidates = [(len(dom[v]), v) for v in dom if len(dom[v]) > 1]
        if not candidates:
            return None
        candidates.sort()
        return candidates[0][1]

    def backtrack(dom):
        ok, dom = propagate(dom)
        if not ok:
            return None
        if is_solved(dom):
            return dom
        var = select_unassigned_variable(dom)
        if var is None:
            return None
        # Try values in increasing order to keep search deterministic
        for value in sorted(dom[var]):
            new_dom = deepcopy(dom)
            new_dom[var] = {value}
            result = backtrack(new_dom)
            if result is not None:
                return result
        return None

    # Solve
    solution_domains = backtrack(domains)
    if solution_domains is None:
        raise RuntimeError("No solution found")

    # Build solution table per house
    header = ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"]
    rows = []
    # Create reverse mapping: for each category, pos -> value
    cat_pos_to_val = {}
    for cat, vals in categories.items():
        mapping = {}
        for v in vals:
            pos = list(solution_domains[v])[0]
            mapping[pos] = v
        # Validate mapping covers all houses (defensive)
        if set(mapping.keys()) != set(houses):
            raise RuntimeError(f"Incomplete assignment for category {cat}")
        cat_pos_to_val[cat] = mapping

    for h in houses:
        row = [
            str(h),
            cat_pos_to_val["Name"][h],
            cat_pos_to_val["PhoneModel"][h],
            cat_pos_to_val["Cigar"][h],
            cat_pos_to_val["Flower"][h],
            cat_pos_to_val["Color"][h],
            cat_pos_to_val["FavoriteSport"][h],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    res = zebra_puzzle_solver()
    print(json.dumps(res, ensure_ascii=False, indent=2))