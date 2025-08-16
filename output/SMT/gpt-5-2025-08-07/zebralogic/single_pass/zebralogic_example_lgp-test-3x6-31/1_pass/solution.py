import json
from z3 import Int, Solver, Distinct, And, sat

def solve_puzzle():
    houses = [1, 2, 3]

    categories = {
        "Name": ["Eric", "Peter", "Arnold"],
        "Drink": ["milk", "water", "tea"],
        "Vacation": ["mountain", "city", "beach"],
        "HouseStyle": ["colonial", "victorian", "ranch"],
        "Animal": ["cat", "bird", "horse"],
        "Birthday": ["jan", "sept", "april"],
    }

    # Create Z3 variables for positions of each attribute value
    pos = {val: Int(f"pos_{val}") for vals in categories.values() for val in vals}

    s = Solver()

    # Domain constraints: all positions are in {1,2,3}
    for v in pos.values():
        s.add(And(v >= 1, v <= 3))

    # Uniqueness constraints within each category
    for cat_vals in categories.values():
        s.add(Distinct([pos[v] for v in cat_vals]))

    # Clues:
    # 1. colonial left of milk
    s.add(pos["colonial"] < pos["milk"])

    # 2. city directly left of victorian
    s.add(pos["city"] + 1 == pos["victorian"])

    # 3. jan directly left of cat
    s.add(pos["jan"] + 1 == pos["cat"])

    # 4. water is mountain
    s.add(pos["water"] == pos["mountain"])

    # 5. horses is Peter
    s.add(pos["horse"] == pos["Peter"])

    # 6. victorian right of beach
    s.add(pos["victorian"] > pos["beach"])

    # 7. Peter is city
    s.add(pos["Peter"] == pos["city"])

    # 8. mountain is april
    s.add(pos["mountain"] == pos["april"])

    # 9. Eric is water
    s.add(pos["Eric"] == pos["water"])

    assert s.check() == sat, "Puzzle is unsatisfiable"
    m = s.model()

    # Build position -> value maps for each category
    pos_to_value = {}
    for cat, vals in categories.items():
        mapping = {}
        for v in vals:
            mapping[m[pos[v]].as_long()] = v
        pos_to_value[cat] = mapping

    header = ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"]
    rows = []
    for h in houses:
        row = [
            str(h),
            pos_to_value["Name"][h],
            pos_to_value["Drink"][h],
            pos_to_value["Vacation"][h],
            pos_to_value["HouseStyle"][h],
            pos_to_value["Animal"][h],
            pos_to_value["Birthday"][h],
        ]
        rows.append(row)

    solution = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(solution))

if __name__ == "__main__":
    solve_puzzle()