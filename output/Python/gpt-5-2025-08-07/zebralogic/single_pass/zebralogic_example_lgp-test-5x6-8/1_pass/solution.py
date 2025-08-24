import json
from copy import deepcopy

def solve():
    # Define categories and values
    categories = {
        "Name": ["Eric", "Peter", "Arnold", "Bob", "Alice"],
        "HouseStyle": ["modern", "craftsman", "ranch", "victorian", "colonial"],
        "Mother": ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"],
        "PhoneModel": ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"],
        "Drink": ["coffee", "water", "root beer", "tea", "milk"],
        "Animal": ["fish", "dog", "horse", "bird", "cat"],
    }

    houses = {1, 2, 3, 4, 5}

    def var(cat, val):
        return f"{cat}:{val}"

    # Initialize domains: every value can be in any house initially
    domains = {var(cat, val): set(houses) for cat, vals in categories.items() for val in vals}
    var_to_cat = {var(cat, val): cat for cat, vals in categories.items() for val in vals}
    cat_to_vars = {cat: [var(cat, val) for val in vals] for cat, vals in categories.items()}

    # Helper to set a domain to singleton
    def set_domain(domains, v, value):
        if value not in domains[v]:
            return False
        if domains[v] == {value}:
            return True
        domains[v] = {value}
        return True

    # Equality constraints (same house)
    equal_pairs = []
    # 4 & 12 & 18 & 19: horse = oneplus 9 = modern = Penny; horse at 3, modern at 3, oneplus 9 at 3, Penny at 3
    equal_pairs += [
        (var("Animal", "horse"), var("PhoneModel", "oneplus 9")),
        (var("Animal", "horse"), var("HouseStyle", "modern")),
        (var("HouseStyle", "modern"), var("Mother", "Penny")),
    ]
    # 9 & 17: tea = Bob
    equal_pairs += [(var("Drink", "tea"), var("Name", "Bob"))]
    # 2 & 22: water = Alice = Janelle
    equal_pairs += [(var("Drink", "water"), var("Name", "Alice")),
                    (var("Drink", "water"), var("Mother", "Janelle"))]
    # 6 & 20: root beer = cat = Peter
    equal_pairs += [(var("Drink", "root beer"), var("Animal", "cat")),
                    (var("Drink", "root beer"), var("Name", "Peter"))]
    # 13 & 14: iphone 13 = milk = dog
    equal_pairs += [(var("PhoneModel", "iphone 13"), var("Drink", "milk")),
                    (var("Drink", "milk"), var("Animal", "dog"))]
    # 15: google pixel 6 = craftsman
    equal_pairs += [(var("PhoneModel", "google pixel 6"), var("HouseStyle", "craftsman"))]
    # 5: ranch = Kailyn
    equal_pairs += [(var("HouseStyle", "ranch"), var("Mother", "Kailyn"))]

    # Relative constraints (varA relation varB) -> position comparisons
    relatives = []
    # 3: colonial > huawei p50
    relatives.append((var("HouseStyle", "colonial"), ">", var("PhoneModel", "huawei p50")))
    # 10: tea > Kailyn
    relatives.append((var("Drink", "tea"), ">", var("Mother", "Kailyn")))
    # 11: root beer < Kailyn
    relatives.append((var("Drink", "root beer"), "<", var("Mother", "Kailyn")))

    # Unary constraints
    # 1: pixel 6 not 1
    domains[var("PhoneModel", "google pixel 6")].discard(1)
    # 7: colonial != 4
    domains[var("HouseStyle", "colonial")].discard(4)
    # 8: bird = 4
    domains[var("Animal", "bird")] = {4}
    # 17: tea = 4
    domains[var("Drink", "tea")] = {4}
    # 9 + 17 implies Bob = 4 via equality propagation
    # 18: horse = 3
    domains[var("Animal", "horse")] = {3}
    # 12: modern = 3 (already coupled with horse)
    domains[var("HouseStyle", "modern")] = {3}
    # 4: oneplus 9 = 3
    domains[var("PhoneModel", "oneplus 9")] = {3}
    # 19: Penny = 3 (modern = Penny)
    domains[var("Mother", "Penny")] = {3}
    # 16: Eric != 2
    domains[var("Name", "Eric")].discard(2)
    # 21: Aniya != 4
    domains[var("Mother", "Aniya")].discard(4)

    # Propagation
    def propagate(domains):
        changed = True
        while changed:
            changed = False

            # Enforce equalities by intersecting domains
            for a, b in equal_pairs:
                da, db = domains[a], domains[b]
                inter = da & db
                if not inter:
                    return False
                if inter != da:
                    domains[a] = set(inter)
                    changed = True
                if inter != db:
                    domains[b] = set(inter)
                    changed = True

            # AllDifferent: remove assigned values from peers
            for cat, vars_in_cat in cat_to_vars.items():
                assigned_vals = set()
                for v in vars_in_cat:
                    if len(domains[v]) == 1:
                        (val,) = tuple(domains[v])
                        assigned_vals.add(val)
                for v in vars_in_cat:
                    if len(domains[v]) > 1:
                        before = set(domains[v])
                        domains[v] -= assigned_vals
                        if not domains[v]:
                            return False
                        if domains[v] != before:
                            changed = True

                # "Only choice for a position" heuristic
                for pos in houses:
                    candidates = [v for v in vars_in_cat if pos in domains[v]]
                    if len(candidates) == 0:
                        return False
                    if len(candidates) == 1:
                        v = candidates[0]
                        if domains[v] != {pos}:
                            domains[v] = {pos}
                            changed = True

            # Relative constraints propagation
            for a, rel, b in relatives:
                Da = domains[a]
                Db = domains[b]
                if rel == ">":
                    # Keep v in Da if v > min(Db)
                    min_Db = min(Db)
                    new_Da = {v for v in Da if v > min_Db}
                    if not new_Da:
                        return False
                    if new_Da != Da:
                        domains[a] = new_Da
                        changed = True
                    # Keep w in Db if w < max(Da)
                    max_Da = max(domains[a])  # after potential update above
                    new_Db = {w for w in Db if w < max_Da}
                    if not new_Db:
                        return False
                    if new_Db != Db:
                        domains[b] = new_Db
                        changed = True
                elif rel == "<":
                    # a < b equivalent logic
                    max_Db = max(Db)
                    new_Da = {v for v in Da if v < max_Db}
                    if not new_Da:
                        return False
                    if new_Da != Da:
                        domains[a] = new_Da
                        changed = True
                    min_Da = min(domains[a])
                    new_Db = {w for w in Db if w > min_Da}
                    if not new_Db:
                        return False
                    if new_Db != Db:
                        domains[b] = new_Db
                        changed = True
                else:
                    return False  # unknown relation

        return True

    # Initial propagation
    if not propagate(domains):
        raise ValueError("Initial constraints are inconsistent.")

    # Backtracking search with MRV
    def is_complete(domains):
        return all(len(domains[v]) == 1 for v in domains)

    def select_unassigned_variable(domains):
        # MRV heuristic
        unassigned = [(len(domains[v]), v) for v in domains if len(domains[v]) > 1]
        if not unassigned:
            return None
        unassigned.sort()
        return unassigned[0][1]

    def backtrack(domains):
        if is_complete(domains):
            return domains
        v = select_unassigned_variable(domains)
        if v is None:
            return domains
        for value in sorted(domains[v]):
            new_domains = deepcopy(domains)
            if not set_domain(new_domains, v, value):
                continue
            if not propagate(new_domains):
                continue
            result = backtrack(new_domains)
            if result is not None:
                return result
        return None

    solution_domains = backtrack(domains)
    if solution_domains is None:
        raise ValueError("No solution found.")

    # Build house-wise solution
    # Invert mapping: for each category, get house -> value
    house_data = {i: {} for i in houses}
    for cat, vals in categories.items():
        for val in vals:
            vname = var(cat, val)
            (pos,) = tuple(solution_domains[vname])
            house_data[pos][cat] = val

    # Prepare JSON output
    header = ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"]
    rows = []
    for i in sorted(houses):
        row = [
            str(i),
            house_data[i]["Name"],
            house_data[i]["HouseStyle"],
            house_data[i]["Mother"],
            house_data[i]["PhoneModel"],
            house_data[i]["Drink"],
            house_data[i]["Animal"],
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
    result = solve()
    print(json.dumps(result, indent=2))