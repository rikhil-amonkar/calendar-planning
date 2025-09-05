import json
from copy import deepcopy

def solve():
    houses = [1, 2, 3, 4, 5, 6]

    categories = {
        "Name": ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"],
        "Food": ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"],
        "Height": ["tall", "average", "super tall", "very short", "very tall", "short"],
        "Drink": ["root beer", "boba tea", "coffee", "water", "tea", "milk"],
        "Pet": ["hamster", "fish", "cat", "dog", "bird", "rabbit"],
        "PhoneModel": ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"],
    }

    # Map each item to its category for easy reference
    item_to_category = {}
    for cat, items in categories.items():
        for it in items:
            item_to_category[it] = cat

    # Variables are all items
    variables = list(item_to_category.keys())

    # Initial domains: each item can be in any house
    domains = {v: set(houses) for v in variables}

    # Constraint structure
    constraints = []  # Each constraint is a dict with type and involved variables

    def add_eq(a, b):
        constraints.append({"type": "eq", "a": a, "b": b})

    def add_left_of(a, b):
        constraints.append({"type": "lt", "a": a, "b": b})

    def add_right_of(a, b):
        constraints.append({"type": "gt", "a": a, "b": b})

    def add_left_of_directly(a, b):
        constraints.append({"type": "dl", "a": a, "b": b})  # a = b - 1

    def add_next_to(a, b):
        constraints.append({"type": "adj", "a": a, "b": b})

    def set_fixed(item, pos):
        domains[item] = {pos}

    def set_not_in(item, pos):
        if pos in domains[item]:
            domains[item].remove(pos)

    # All-different within category handled by propagation logic

    # Apply puzzle constraints:

    # 1. The person who uses an iPhone 13 is in the third house.
    set_fixed("iphone 13", 3)

    # 2. Bob is the person who is tall.
    add_eq("Bob", "tall")

    # 3. The person who loves the soup is in the second house.
    set_fixed("soup", 2)

    # 4. The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
    add_left_of_directly("root beer", "xiaomi mi 11")

    # 5. The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
    add_left_of_directly("huawei p50", "grilled cheese")

    # 6. The person who loves stir fry is the person who likes milk.
    add_eq("stir fry", "milk")

    # 7. The person who loves eating grilled cheese is the person who is tall.
    add_eq("grilled cheese", "tall")

    # 8. The person who uses a Xiaomi Mi 11 is the coffee drinker.
    add_eq("xiaomi mi 11", "coffee")

    # 9. The person who uses a OnePlus 9 is Arnold.
    add_eq("oneplus 9", "Arnold")

    # 10. The person who owns a rabbit is not in the fifth house.
    set_not_in("rabbit", 5)

    # 11. The person with a pet hamster is somewhere to the right of the person who uses a Google Pixel 6.
    add_right_of("hamster", "google pixel 6")

    # 12. The person who is super tall is the person with an aquarium of fish.
    add_eq("super tall", "fish")

    # 13. The person with an aquarium of fish is Alice.
    add_eq("fish", "Alice")

    # 14. The tea drinker is directly left of the person who is a pizza lover.
    add_left_of_directly("tea", "pizza")

    # 15. The person who uses a Samsung Galaxy S21 is Carol.
    add_eq("samsung galaxy s21", "Carol")

    # 16. The person who is a pizza lover is the person who is short.
    add_eq("pizza", "short")

    # 17. Arnold is the person who is very tall.
    add_eq("Arnold", "very tall")

    # 18. The person who loves the spaghetti eater is the person who uses a Google Pixel 6.
    # Interpreting as: The spaghetti eater uses a Google Pixel 6.
    add_eq("spaghetti", "google pixel 6")

    # 19. The boba tea drinker is somewhere to the right of the person who loves the soup.
    add_right_of("boba tea", "soup")

    # 20. The person with a pet hamster is not in the fifth house.
    set_not_in("hamster", 5)

    # 21. The person who is very tall is not in the second house.
    set_not_in("very tall", 2)

    # 22. The person who is super tall is somewhere to the left of Peter.
    add_left_of("super tall", "Peter")

    # 23. The person who is very short is the person who loves the spaghetti eater.
    # Interpreting as: The spaghetti eater is the very short person.
    add_eq("very short", "spaghetti")

    # 24. The person who keeps a pet bird is somewhere to the left of the person who loves the spaghetti eater.
    add_left_of("bird", "spaghetti")

    # 25. The person with an aquarium of fish is directly left of Eric.
    add_left_of_directly("fish", "Eric")

    # 26. The person who owns a dog is the person who likes milk.
    add_eq("dog", "milk")

    # Build adjacency list for constraints referencing variables
    var_to_constraints = {v: [] for v in variables}
    for idx, c in enumerate(constraints):
        var_to_constraints[c["a"]].append(idx)
        var_to_constraints[c["b"]].append(idx)

    # Helper: apply constraint revision (AC-3 like)
    def revise(domains, c):
        changed = False
        a, b = c["a"], c["b"]
        da = domains[a]
        db = domains[b]
        if c["type"] == "eq":
            new_da = da & db
            new_db = db & da
            if new_da != da:
                domains[a] = new_da
                changed = True
            if new_db != db:
                domains[b] = new_db
                changed = True
        elif c["type"] == "dl":  # a = b - 1
            new_da = set(x for x in da if x + 1 in db)
            new_db = set(y for y in db if y - 1 in da)
            if new_da != da:
                domains[a] = new_da
                changed = True
            if new_db != db:
                domains[b] = new_db
                changed = True
        elif c["type"] == "lt":  # a < b
            new_da = set(x for x in da if any(y > x for y in db))
            new_db = set(y for y in db if any(x < y for x in da))
            if new_da != da:
                domains[a] = new_da
                changed = True
            if new_db != db:
                domains[b] = new_db
                changed = True
        elif c["type"] == "gt":  # a > b
            # a > b  <=>  b < a
            new_da = set(x for x in da if any(y < x for y in db))
            new_db = set(y for y in db if any(x > y for x in da))
            if new_da != da:
                domains[a] = new_da
                changed = True
            if new_db != db:
                domains[b] = new_db
                changed = True
        elif c["type"] == "adj":
            new_da = set(x for x in da if any(abs(x - y) == 1 for y in db))
            new_db = set(y for y in db if any(abs(x - y) == 1 for x in da))
            if new_da != da:
                domains[a] = new_da
                changed = True
            if new_db != db:
                domains[b] = new_db
                changed = True
        return changed

    # Propagate all constraints and simple all-different singleton eliminations
    def propagate(domains):
        # AC-3 for binary constraints
        changed = True
        while changed:
            changed = False
            # Apply binary constraints revisions
            for c in constraints:
                if revise(domains, c):
                    changed = True
                    # If any domain is empty, fail early
                    for v in variables:
                        if len(domains[v]) == 0:
                            return False
            # Singleton propagation for all-different within categories
            for cat, items in categories.items():
                # Collect assigned positions in this category
                singles = [next(iter(domains[it])) for it in items if len(domains[it]) == 1]
                for it in items:
                    if len(domains[it]) > 1:
                        new_dom = set(x for x in domains[it] if x not in singles)
                        if new_dom != domains[it]:
                            domains[it] = new_dom
                            changed = True
                            if len(domains[it]) == 0:
                                return False
        # Additional quick check: within any category, ensure that the union of domains has size at least number of items left
        for cat, items in categories.items():
            unassigned = [it for it in items if len(domains[it]) > 1]
            if unassigned:
                union = set()
                for it in unassigned:
                    union |= domains[it]
                if len(union) < len(unassigned):
                    return False
        return True

    # Initial propagation
    if not propagate(domains):
        raise RuntimeError("Initial constraints lead to no solution")

    # Backtracking search
    def is_solved(domains):
        return all(len(domains[v]) == 1 for v in variables)

    def select_unassigned_variable(domains):
        # Pick variable with smallest domain > 1
        uns = [(v, len(domains[v])) for v in variables if len(domains[v]) > 1]
        if not uns:
            return None
        uns.sort(key=lambda x: x[1])
        return uns[0][0]

    def backtrack(domains):
        if is_solved(domains):
            return domains
        var = select_unassigned_variable(domains)
        if var is None:
            return None
        # Try values in domain (order can be natural)
        for val in sorted(domains[var]):
            new_domains = deepcopy(domains)
            new_domains[var] = {val}
            if propagate(new_domains):
                result = backtrack(new_domains)
                if result is not None:
                    return result
        return None

    solution_domains = backtrack(domains)
    if solution_domains is None:
        raise RuntimeError("No solution found")

    # Construct output rows by house number
    # For each house, find the item in each category that is assigned to that house
    # Build pos->item per category
    pos_to_item = {cat: {pos: None for pos in houses} for cat in categories}
    for item, dom in solution_domains.items():
        pos = next(iter(dom))
        cat = item_to_category[item]
        pos_to_item[cat][pos] = item

    rows = []
    for pos in houses:
        row = [
            str(pos),
            pos_to_item["Name"][pos],
            pos_to_item["Food"][pos],
            pos_to_item["Height"][pos],
            pos_to_item["Drink"][pos],
            pos_to_item["Pet"][pos],
            pos_to_item["PhoneModel"][pos],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    solve()