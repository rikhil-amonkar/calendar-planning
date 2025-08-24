import json
import copy

def solve():
    houses = set(range(1, 7))  # 1..6

    categories = {
        "Name": ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"],
        "Food": ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"],
        "Height": ["tall", "average", "super tall", "very short", "very tall", "short"],
        "Drink": ["root beer", "boba tea", "coffee", "water", "tea", "milk"],
        "Pet": ["hamster", "fish", "cat", "dog", "bird", "rabbit"],
        "PhoneModel": ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"],
    }

    # Initialize domains: each specific value can be any house 1..6
    domains = {}
    for cat, vals in categories.items():
        for v in vals:
            domains[(cat, v)] = set(houses)

    # Constraint helpers
    equals = []           # list of tuple(varA, varB) meaning varA house == varB house
    adj_left = []         # list of tuple(varA, varB) meaning varA is directly left of varB (A = B-1)
    left_of = []          # list of tuple(varA, varB) meaning varA is somewhere left of varB (A < B)
    right_of = []         # list of tuple(varA, varB) meaning varA is somewhere right of varB (A > B)
    notequals_house = []  # list of (var, house) meaning var cannot be at that house

    def var(cat, val):
        return (cat, val)

    # Apply fixed-position constraints
    # 1. iPhone 13 in the third house.
    domains[var("PhoneModel", "iphone 13")] = {3}

    # 3. Soup is in the second house.
    domains[var("Food", "soup")] = {2}

    # 21. The person who is very tall is not in the second house.
    domains[var("Height", "very tall")] -= {2}

    # 10. Rabbit not in fifth house.
    notequals_house.append((var("Pet", "rabbit"), 5))
    # 20. Hamster not in fifth house.
    notequals_house.append((var("Pet", "hamster"), 5))

    # Equality constraints
    # 2. Bob is tall.
    equals.append((var("Name", "Bob"), var("Height", "tall")))
    # 7. grilled cheese is tall.
    equals.append((var("Food", "grilled cheese"), var("Height", "tall")))
    # 6. stir fry is milk.
    equals.append((var("Food", "stir fry"), var("Drink", "milk")))
    # 8. Xiaomi Mi 11 is the coffee drinker.
    equals.append((var("PhoneModel", "xiaomi mi 11"), var("Drink", "coffee")))
    # 9. OnePlus 9 is Arnold.
    equals.append((var("PhoneModel", "oneplus 9"), var("Name", "Arnold")))
    # 15. Samsung Galaxy S21 is Carol.
    equals.append((var("PhoneModel", "samsung galaxy s21"), var("Name", "Carol")))
    # 17. Arnold is very tall.
    equals.append((var("Name", "Arnold"), var("Height", "very tall")))
    # 12. super tall is fish.
    equals.append((var("Height", "super tall"), var("Pet", "fish")))
    # 13. fish is Alice.
    equals.append((var("Pet", "fish"), var("Name", "Alice")))
    # 18. spaghetti eater uses Google Pixel 6.
    equals.append((var("Food", "spaghetti"), var("PhoneModel", "google pixel 6")))
    # 23. very short is the spaghetti eater.
    equals.append((var("Height", "very short"), var("Food", "spaghetti")))
    # 26. dog is milk.
    equals.append((var("Pet", "dog"), var("Drink", "milk")))

    # Adjacency constraints (directly left of)
    # 4. root beer directly left of Xiaomi.
    adj_left.append((var("Drink", "root beer"), var("PhoneModel", "xiaomi mi 11")))
    # 5. Huawei P50 directly left of grilled cheese.
    adj_left.append((var("PhoneModel", "huawei p50"), var("Food", "grilled cheese")))
    # 14. tea directly left of pizza.
    adj_left.append((var("Drink", "tea"), var("Food", "pizza")))
    # 25. fish directly left of Eric.
    adj_left.append((var("Pet", "fish"), var("Name", "Eric")))

    # Left/right (non-adjacent unless forced)
    # 22. super tall is somewhere to the left of Peter.
    left_of.append((var("Height", "super tall"), var("Name", "Peter")))
    # 24. bird is somewhere to the left of spaghetti eater.
    left_of.append((var("Pet", "bird"), var("Food", "spaghetti")))
    # 11. hamster somewhere to the right of Google Pixel 6.
    right_of.append((var("Pet", "hamster"), var("PhoneModel", "google pixel 6")))
    # 19. boba tea is somewhere to the right of soup.
    right_of.append((var("Drink", "boba tea"), var("Food", "soup")))
    # 16. pizza is short.
    equals.append((var("Food", "pizza"), var("Height", "short")))

    # Helper propagation functions
    def propagate(dom):
        changed = True
        while changed:
            changed = False

            # Apply notequals
            for v, h in notequals_house:
                if h in dom[v]:
                    dom[v] = set(x for x in dom[v] if x != h)
                    if not dom[v]:
                        return False
                    changed = True

            # Equalities: intersect domains
            for a, b in equals:
                inter = dom[a] & dom[b]
                if not inter:
                    return False
                if inter != dom[a]:
                    dom[a] = set(inter)
                    changed = True
                if inter != dom[b]:
                    dom[b] = set(inter)
                    changed = True

            # Adjacency left: a = b - 1
            for a, b in adj_left:
                new_a = set(h for h in dom[a] if (h + 1) in dom[b])
                new_b = set(h for h in dom[b] if (h - 1) in dom[a])
                if not new_a or not new_b:
                    return False
                if new_a != dom[a]:
                    dom[a] = new_a
                    changed = True
                if new_b != dom[b]:
                    dom[b] = new_b
                    changed = True

            # Left-of: a < b
            for a, b in left_of:
                # For each h in a, need some k in b with h < k
                new_a = set(h for h in dom[a] if any(h < k for k in dom[b]))
                new_b = set(k for k in dom[b] if any(h < k for h in dom[a]))
                if not new_a or not new_b:
                    return False
                if new_a != dom[a]:
                    dom[a] = new_a
                    changed = True
                if new_b != dom[b]:
                    dom[b] = new_b
                    changed = True

            # Right-of: a > b
            for a, b in right_of:
                new_a = set(h for h in dom[a] if any(k < h for k in dom[b]))
                new_b = set(k for k in dom[b] if any(k < h for h in dom[a]))
                if not new_a or not new_b:
                    return False
                if new_a != dom[a]:
                    dom[a] = new_a
                    changed = True
                if new_b != dom[b]:
                    dom[b] = new_b
                    changed = True

            # All-different per category
            for cat, vals in categories.items():
                # Collect singletons
                singles = [next(iter(dom[(cat, v)])) for v in vals if len(dom[(cat, v)]) == 1]
                # Remove these houses from others in same category
                for v in vals:
                    key = (cat, v)
                    if len(dom[key]) > 1:
                        new_set = dom[key] - set(singles)
                        if not new_set:
                            return False
                        if new_set != dom[key]:
                            dom[key] = new_set
                            changed = True

        return True

    # Initial propagation
    if not propagate(domains):
        raise RuntimeError("Initial constraints inconsistent")

    # Backtracking search
    all_vars = list(domains.keys())

    def is_complete(dom):
        return all(len(dom[v]) == 1 for v in dom)

    def select_unassigned(dom):
        # Choose var with smallest domain > 1
        unassigned = [v for v in all_vars if len(dom[v]) > 1]
        if not unassigned:
            return None
        return min(unassigned, key=lambda v: len(dom[v]))

    def backtrack(dom):
        if is_complete(dom):
            return dom
        var_choice = select_unassigned(dom)
        if var_choice is None:
            return None
        for val in sorted(dom[var_choice]):
            new_dom = copy.deepcopy(dom)
            new_dom[var_choice] = {val}
            if propagate(new_dom):
                result = backtrack(new_dom)
                if result is not None:
                    return result
        return None

    solution_domains = backtrack(domains)
    if solution_domains is None:
        raise RuntimeError("No solution found")

    # Build output per house
    # Invert mapping: for each category, find the value at each house
    result_rows = []
    for h in range(1, 7):
        name = next(v for v in categories["Name"] if list(solution_domains[("Name", v)])[0] == h)
        food = next(v for v in categories["Food"] if list(solution_domains[("Food", v)])[0] == h)
        height = next(v for v in categories["Height"] if list(solution_domains[("Height", v)])[0] == h)
        drink = next(v for v in categories["Drink"] if list(solution_domains[("Drink", v)])[0] == h)
        pet = next(v for v in categories["Pet"] if list(solution_domains[("Pet", v)])[0] == h)
        phone = next(v for v in categories["PhoneModel"] if list(solution_domains[("PhoneModel", v)])[0] == h)
        result_rows.append([str(h), name, food, height, drink, pet, phone])

    output = {
        "solution": {
            "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
            "rows": result_rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))


if __name__ == "__main__":
    solve()