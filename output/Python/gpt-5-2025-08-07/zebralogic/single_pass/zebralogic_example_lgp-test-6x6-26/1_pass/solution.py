import json
import copy

def solve_puzzle():
    houses = list(range(1, 7))  # 1..6

    categories = {
        "Name": ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"],
        "PhoneModel": ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"],
        "Cigar": ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"],
        "Flower": ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"],
        "Color": ["yellow", "red", "green", "blue", "white", "purple"],
        "FavoriteSport": ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"],
    }

    # Build item to category map
    item_to_category = {}
    for cat, items in categories.items():
        for it in items:
            item_to_category[it] = cat

    # Initialize domains
    domains = {item: set(houses) for item in item_to_category}

    # Constraint containers
    eq_pairs = []            # (A, B) -> same house
    direct_left_pairs = []   # (A, B) -> A immediately left of B
    left_of_pairs = []       # (A, B) -> A somewhere left of B
    next_to_pairs = []       # (A, B) -> A next to B (undirected)
    distance_pairs = []      # (A, B, d) -> |pos(A)-pos(B)| = d

    # Helper to add equality (same house)
    def eq(a, b):
        eq_pairs.append((a, b))

    # Helper to add direct left A is immediately left of B
    def direct_left(a, b):
        direct_left_pairs.append((a, b))

    # Helper to add somewhere left
    def left_of(a, b):
        left_of_pairs.append((a, b))

    # Helper to add adjacent
    def next_to(a, b):
        next_to_pairs.append((a, b))

    # Helper to add exact distance
    def distance(a, b, d):
        distance_pairs.append((a, b, d))

    # Apply given clues:

    # 1. The person who uses a OnePlus 9 is in the second house.
    domains["oneplus 9"] = {2}

    # 2. The person who uses a Xiaomi Mi 11 is somewhere to the left of the person who uses a Huawei P50.
    left_of("xiaomi mi 11", "huawei p50")

    # 3. Carol is the person who loves a carnations arrangement.
    eq("Carol", "carnations")

    # 4. The person who loves purple is directly left of the person partial to Pall Mall.
    direct_left("purple", "pall mall")

    # 5. The person whose favorite color is green is the person who smokes Blue Master.
    eq("green", "blue master")

    # 6. The person who loves yellow and the person who loves blue are next to each other.
    next_to("yellow", "blue")

    # 7. Eric is somewhere to the right of the person who uses a Samsung Galaxy S21.
    left_of("samsung galaxy s21", "Eric")

    # 8. There are two houses between Carol and the person who loves a bouquet of daffodils.
    distance("Carol", "daffodils", 3)

    # 9. The Prince smoker is the person who loves basketball.
    eq("prince", "basketball")

    # 10. The Dunhill smoker is the person who loves volleyball.
    eq("dunhill", "volleyball")

    # 11. The person who loves swimming is the person who uses a Google Pixel 6.
    eq("swimming", "google pixel 6")

    # 12. The person who uses a Huawei P50 is directly left of the person who loves white.
    direct_left("huawei p50", "white")

    # 13. The person who uses a OnePlus 9 and the person who loves the rose bouquet are next to each other.
    next_to("oneplus 9", "roses")

    # 14. The person who loves the boquet of iris is somewhere to the left of Eric.
    left_of("iris", "Eric")

    # 15. The Dunhill smoker is Peter.
    eq("dunhill", "Peter")

    # 16. The person who loves blue is Peter.
    eq("blue", "Peter")

    # 17. The person who loves the vase of tulips is Bob.
    eq("tulips", "Bob")

    # 18. Alice is in the first house.
    domains["Alice"] = {1}

    # 19. The person who loves baseball is directly left of the person who smokes Blue Master.
    direct_left("baseball", "blue master")

    # 20. The person who uses a Google Pixel 6 is somewhere to the right of the person who smokes many unique blends.
    left_of("blends", "google pixel 6")

    # 21. The person who loves soccer is Carol.
    eq("soccer", "Carol")

    # 22. The person who loves a carnations arrangement is directly left of the person who smokes many unique blends.
    direct_left("carnations", "blends")

    # 23. Eric is the person who smokes many unique blends.
    eq("Eric", "blends")

    # 24. The person who loves volleyball is the person who uses an iPhone 13.
    eq("volleyball", "iphone 13")

    # Propagation utilities
    def propagate(dom):
        changed = True
        while changed:
            changed = False

            # Apply equality constraints
            for a, b in eq_pairs:
                inter = dom[a] & dom[b]
                if inter != dom[a]:
                    dom[a] = set(inter)
                    changed = True
                if inter != dom[b]:
                    dom[b] = set(inter)
                    changed = True

            # Apply direct left constraints: A = B - 1
            for a, b in direct_left_pairs:
                new_a = {x for x in dom[a] if (x + 1) in dom[b]}
                new_b = {y for y in dom[b] if (y - 1) in dom[a]}
                if new_a != dom[a]:
                    dom[a] = new_a
                    changed = True
                if new_b != dom[b]:
                    dom[b] = new_b
                    changed = True

            # Apply somewhere left constraints: A < B
            for a, b in left_of_pairs:
                new_a = {x for x in dom[a] if any(y > x for y in dom[b])}
                new_b = {y for y in dom[b] if any(x < y for x in dom[a])}
                if new_a != dom[a]:
                    dom[a] = new_a
                    changed = True
                if new_b != dom[b]:
                    dom[b] = new_b
                    changed = True

            # Apply next_to constraints: |A - B| = 1
            for a, b in next_to_pairs:
                new_a = {x for x in dom[a] if (x - 1) in dom[b] or (x + 1) in dom[b]}
                new_b = {y for y in dom[b] if (y - 1) in dom[a] or (y + 1) in dom[a]}
                if new_a != dom[a]:
                    dom[a] = new_a
                    changed = True
                if new_b != dom[b]:
                    dom[b] = new_b
                    changed = True

            # Apply exact distance constraints: |A - B| = d
            for a, b, d in distance_pairs:
                new_a = {x for x in dom[a] if ((x - d) in dom[b] or (x + d) in dom[b])}
                new_b = {y for y in dom[b] if ((y - d) in dom[a] or (y + d) in dom[a])}
                if new_a != dom[a]:
                    dom[a] = new_a
                    changed = True
                if new_b != dom[b]:
                    dom[b] = new_b
                    changed = True

            # Category uniqueness propagation (simple)
            for cat, items in categories.items():
                # If an item is fixed to a house, remove that house from other items in same category
                fixed_houses = [next(iter(dom[it])) for it in items if len(dom[it]) == 1]
                for it in items:
                    if len(dom[it]) > 1:
                        new_set = set(x for x in dom[it] if x not in fixed_houses)
                        if new_set != dom[it]:
                            dom[it] = new_set
                            changed = True

                # Hidden singles: if a house is only available to one item in the category, assign it
                for h in houses:
                    holders = [it for it in items if h in dom[it]]
                    if len(holders) == 1 and dom[holders[0]] != {h}:
                        dom[holders[0]] = {h}
                        changed = True

            # Early failure check
            for it, dset in dom.items():
                if len(dset) == 0:
                    return False  # contradiction
        return True

    def is_solved(dom):
        return all(len(v) == 1 for v in dom.values())

    def choose_var(dom):
        # choose item with smallest domain > 1
        unsolved = [(it, dom[it]) for it in dom if len(dom[it]) > 1]
        if not unsolved:
            return None
        it, dset = min(unsolved, key=lambda x: len(x[1]))
        return it

    def backtrack(dom):
        if not propagate(dom):
            return None
        if is_solved(dom):
            return dom
        var = choose_var(dom)
        if var is None:
            return None
        for val in sorted(dom[var]):
            new_dom = copy.deepcopy(dom)
            new_dom[var] = {val}
            res = backtrack(new_dom)
            if res is not None:
                return res
        return None

    solution_domains = backtrack(copy.deepcopy(domains))
    if solution_domains is None:
        raise ValueError("No solution found")

    # Build final mapping item -> house (int)
    final_pos = {item: next(iter(hs)) for item, hs in solution_domains.items()}

    # Build per category house->item mapping
    cat_house_item = {}
    for cat, items in categories.items():
        mapping = {h: None for h in houses}
        for it in items:
            h = final_pos[it]
            if mapping[h] is not None:
                raise ValueError(f"Duplicate assignment in category {cat} for house {h}")
            mapping[h] = it
        cat_house_item[cat] = mapping

    # Prepare JSON output
    header = ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"]
    rows = []
    for h in houses:
        row = [
            str(h),
            cat_house_item["Name"][h],
            cat_house_item["PhoneModel"][h],
            cat_house_item["Cigar"][h],
            cat_house_item["Flower"][h],
            cat_house_item["Color"][h],
            cat_house_item["FavoriteSport"][h],
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