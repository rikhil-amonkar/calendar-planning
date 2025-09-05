import json
from copy import deepcopy

def zebra_solver():
    houses = [1, 2, 3, 4, 5, 6]

    categories = {
        "Name": ["Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"],
        "HouseStyle": ["ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"],
        "Food": ["pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"],
        "Vacation": ["cultural", "cruise", "mountain", "camping", "city", "beach"],
        "Height": ["average", "very tall", "very short", "short", "tall", "super tall"],
        "Cigar": ["yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"],
    }

    # Helper to refer to items
    def it(cat, val):
        return (cat, val)

    # Initialize domains
    domains = {}
    for cat, items in categories.items():
        for val in items:
            domains[it(cat, val)] = set(houses)

    # Constraint containers
    equals = []            # list of (a, b) meaning same house
    left_of = []           # list of (a, b) meaning a is somewhere to the left of b
    immediate_left_of = [] # list of (a, b) meaning a is immediately left of b
    distance_eq = []       # list of (a, b, d) meaning |pos(a) - pos(b)| = d
    next_to = []           # list of (a, b) meaning |pos(a) - pos(b)| = 1
    not_equals = []        # list of (a, b) meaning a and b are not in the same house
    not_positions = {}     # dict of item -> positions to remove
    fixed_positions = {}   # dict of item -> fixed position

    # Apply direct constraints from clues:

    # 1. Alice is in the fifth house.
    fixed_positions[it("Name", "Alice")] = 5

    # 2. stir fry = colonial
    equals.append((it("Food", "stir fry"), it("HouseStyle", "colonial")))

    # 3 and 14 combined: Alice is the person who loves the spaghetti eater; that person resides in a Victorian house.
    # => Alice resides in a Victorian house, and Alice is NOT the spaghetti eater.
    equals.append((it("Name", "Alice"), it("HouseStyle", "victorian")))
    not_equals.append((it("Name", "Alice"), it("Food", "spaghetti")))

    # 4. Arnold = stew
    equals.append((it("Name", "Arnold"), it("Food", "stew")))

    # 5. one house between average and Peter => distance 2
    distance_eq.append((it("Height", "average"), it("Name", "Peter"), 2))

    # 6. Craftsman not in the third house.
    not_positions[it("HouseStyle", "craftsman")] = {3}

    # 7. average = stir fry
    equals.append((it("Height", "average"), it("Food", "stir fry")))

    # 8. beach = ranch
    equals.append((it("Vacation", "beach"), it("HouseStyle", "ranch")))

    # 9. Eric is in the fourth house.
    fixed_positions[it("Name", "Eric")] = 4

    # 10. distance 2 between colonial and camping
    distance_eq.append((it("HouseStyle", "colonial"), it("Vacation", "camping"), 2))

    # 11. mountain = yellow monster
    equals.append((it("Vacation", "mountain"), it("Cigar", "yellow monster")))

    # 12. mountain = very tall
    equals.append((it("Vacation", "mountain"), it("Height", "very tall")))

    # 13. mountain next to Dunhill
    next_to.append((it("Vacation", "mountain"), it("Cigar", "dunhill")))

    # 15. tall = beach
    equals.append((it("Height", "tall"), it("Vacation", "beach")))

    # 16. tall left of Victorian
    left_of.append((it("Height", "tall"), it("HouseStyle", "victorian")))

    # 17. stir fry directly left of Bob; since stir fry = colonial, use stir fry (equals will propagate)
    immediate_left_of.append((it("Food", "stir fry"), it("Name", "Bob")))

    # 18. modern left of Alice
    left_of.append((it("HouseStyle", "modern"), it("Name", "Alice")))

    # 19. Craftsman left of short
    left_of.append((it("HouseStyle", "craftsman"), it("Height", "short")))

    # 20. stir fry left of Prince; stir fry = colonial
    left_of.append((it("Food", "stir fry"), it("Cigar", "prince")))

    # 21. grilled cheese and super tall distance 3
    distance_eq.append((it("Food", "grilled cheese"), it("Height", "super tall"), 3))

    # 22. ranch = Blue Master
    equals.append((it("HouseStyle", "ranch"), it("Cigar", "blue master")))

    # 23. blends directly left of Blue Master
    immediate_left_of.append((it("Cigar", "blends"), it("Cigar", "blue master")))

    # 24. cultural = pizza
    equals.append((it("Vacation", "cultural"), it("Food", "pizza")))

    # 25. pizza left of cruise (pizza=cultural)
    left_of.append((it("Food", "pizza"), it("Vacation", "cruise")))

    # Helper: enforce all-different within categories after assignment
    category_items = {cat: [it(cat, v) for v in vals] for cat, vals in categories.items()}

    # Initialize by applying fixed positions and not_positions
    for item, pos in fixed_positions.items():
        domains[item] = {pos}
    for item, bad_pos in not_positions.items():
        domains[item] -= set(bad_pos)

    # Propagation helpers
    def enforce_all_different(dom):
        changed = False
        for cat, items in category_items.items():
            # Collect singles and detect duplicates
            singles = [next(iter(dom[item])) for item in items if len(dom[item]) == 1]
            if len(singles) != len(set(singles)):
                # Two different items in the same category share the same fixed position -> impossible
                return None, True
            taken = set(singles)
            for item in items:
                if len(dom[item]) > 1:
                    newset = dom[item] - taken
                    if not newset:
                        return None, True
                    if newset != dom[item]:
                        dom[item] = newset
                        changed = True
        return changed, False

    def apply_equals(dom):
        changed = False
        for a, b in equals:
            A = dom[a]
            B = dom[b]
            inter = A & B
            if not inter:
                return None, True
            if inter != A:
                dom[a] = set(inter)
                changed = True
            if inter != B:
                dom[b] = set(inter)
                changed = True
        return changed, False

    def apply_not_equals(dom):
        changed = False
        for a, b in not_equals:
            A = dom[a]
            B = dom[b]
            # If both are singletons and equal -> fail
            if len(A) == 1 and len(B) == 1 and A == B:
                return None, True
            # If A is single, remove its value from B
            if len(A) == 1:
                v = next(iter(A))
                if v in B:
                    newB = set(B)
                    newB.discard(v)
                    if not newB:
                        return None, True
                    if newB != B:
                        dom[b] = newB
                        changed = True
            # If B is single, remove its value from A
            if len(B) == 1:
                v = next(iter(B))
                if v in A:
                    newA = set(A)
                    newA.discard(v)
                    if not newA:
                        return None, True
                    if newA != A:
                        dom[a] = newA
                        changed = True
        return changed, False

    def apply_left_of(dom):
        changed = False
        for a, b in left_of:
            A = dom[a]
            B = dom[b]
            if not A or not B:
                return None, True
            newA = {p for p in A if any(p < q for q in B)}
            newB = {q for q in B if any(p < q for p in A)}
            if not newA or not newB:
                return None, True
            if newA != A:
                dom[a] = newA
                changed = True
            if newB != B:
                dom[b] = newB
                changed = True
        return changed, False

    def apply_immediate_left_of(dom):
        changed = False
        for a, b in immediate_left_of:
            A = dom[a]
            B = dom[b]
            if not A or not B:
                return None, True
            newA = {p for p in A if (p + 1) in B}
            newB = {q for q in B if (q - 1) in A}
            if not newA or not newB:
                return None, True
            if newA != A:
                dom[a] = newA
                changed = True
            if newB != B:
                dom[b] = newB
                changed = True
        return changed, False

    def apply_next_to(dom):
        changed = False
        for a, b in next_to:
            A = dom[a]
            B = dom[b]
            if not A or not B:
                return None, True
            newA = {p for p in A if (p - 1) in B or (p + 1) in B}
            newB = {q for q in B if (q - 1) in A or (q + 1) in A}
            if not newA or not newB:
                return None, True
            if newA != A:
                dom[a] = newA
                changed = True
            if newB != B:
                dom[b] = newB
                changed = True
        return changed, False

    def apply_distance(dom):
        changed = False
        for a, b, d in distance_eq:
            A = dom[a]
            B = dom[b]
            if not A or not B:
                return None, True
            newA = {p for p in A if (p - d) in B or (p + d) in B}
            newB = {q for q in B if (q - d) in A or (q + d) in A}
            if not newA or not newB:
                return None, True
            if newA != A:
                dom[a] = newA
                changed = True
            if newB != B:
                dom[b] = newB
                changed = True
        return changed, False

    def propagate(dom):
        while True:
            # Check for empties early
            for k, v in dom.items():
                if not v:
                    return False
            changed = False
            # Apply all-different
            ch, fail = enforce_all_different(dom)
            if fail:
                return False
            if ch:
                changed = True
            # Apply equals
            ch, fail = apply_equals(dom)
            if fail:
                return False
            if ch:
                changed = True
            # Apply disequality
            ch, fail = apply_not_equals(dom)
            if fail:
                return False
            if ch:
                changed = True
            # Apply immediate left-of
            ch, fail = apply_immediate_left_of(dom)
            if fail:
                return False
            if ch:
                changed = True
            # Apply left-of
            ch, fail = apply_left_of(dom)
            if fail:
                return False
            if ch:
                changed = True
            # Apply next-to
            ch, fail = apply_next_to(dom)
            if fail:
                return False
            if ch:
                changed = True
            # Apply distance constraints
            ch, fail = apply_distance(dom)
            if fail:
                return False
            if ch:
                changed = True
            # Re-apply all-different after structural changes
            ch, fail = enforce_all_different(dom)
            if fail:
                return False
            if ch:
                changed = True
            # If no more changes, stop
            if not changed:
                break
        # Final emptiness check
        for k, v in dom.items():
            if not v:
                return False
        return True

    def is_solved(dom):
        # All items singletons AND all-different per category
        if not all(len(v) == 1 for v in dom.values()):
            return False
        # Check all-different per category strictly (no duplicates)
        for cat, items in category_items.items():
            vals = [next(iter(dom[item])) for item in items]
            if len(vals) != len(set(vals)):
                return False
        return True

    def select_unassigned(dom):
        # choose the item with smallest domain > 1
        items = [k for k, v in dom.items() if len(v) > 1]
        if not items:
            return None
        return min(items, key=lambda k: len(dom[k]))

    def backtrack(dom):
        if not propagate(dom):
            return None
        if is_solved(dom):
            return dom
        var = select_unassigned(dom)
        if var is None:
            return None
        # Try values in sorted order
        for val in sorted(dom[var]):
            new_dom = deepcopy(dom)
            new_dom[var] = {val}
            res = backtrack(new_dom)
            if res is not None:
                return res
        return None

    solution_domains = backtrack(domains)
    if solution_domains is None:
        raise RuntimeError("No solution found")

    # Build the final table
    header = ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"]
    rows = []
    for h in houses:
        row = [str(h)]
        for cat in ["Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"]:
            # find the item in this category that is assigned to house h
            found = None
            for val in categories[cat]:
                if list(solution_domains[it(cat, val)]) == [h]:
                    found = val
                    break
            if found is None:
                raise RuntimeError(f"Incomplete assignment for house {h}, category {cat}")
            row.append(found)
        rows.append(row)

    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = zebra_solver()
    print(json.dumps(result, ensure_ascii=False))