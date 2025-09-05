import json
from z3 import Solver, Int, Distinct, And, Or, Abs, sat

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    names = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    children = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]

    # Create Z3 variables for positions of each name and each child
    name_pos = {n: Int(f"pos_name_{n}") for n in names}
    child_pos = {c: Int(f"pos_child_{c}") for c in children}

    s = Solver()

    # Domain constraints: positions are 1..5
    for v in name_pos.values():
        s.add(And(v >= 1, v <= 5))
    for v in child_pos.values():
        s.add(And(v >= 1, v <= 5))

    # Uniqueness constraints within categories
    s.add(Distinct([name_pos[n] for n in names]))
    s.add(Distinct([child_pos[c] for c in children]))

    # Clues:
    # 1. Bob is somewhere to the left of the person's child is named Samantha.
    s.add(name_pos["Bob"] < child_pos["Samantha"])

    # 2. The person who is the mother of Timothy is somewhere to the left of the person's child is named Samantha.
    s.add(child_pos["Timothy"] < child_pos["Samantha"])

    # 3. The person's child is named Fred is in the second house.
    s.add(child_pos["Fred"] == 2)

    # 4. There is one house between Alice and the person's child is named Samantha.
    s.add(Abs(name_pos["Alice"] - child_pos["Samantha"]) == 2)

    # 5. Eric is not in the third house.
    s.add(name_pos["Eric"] != 3)

    # 6. Bob is not in the third house.
    s.add(name_pos["Bob"] != 3)

    # 7. The person's child is named Fred is directly left of the person's child is named Bella.
    s.add(child_pos["Fred"] + 1 == child_pos["Bella"])

    # 8. The person's child is named Samantha is somewhere to the left of Peter.
    s.add(child_pos["Samantha"] < name_pos["Peter"])

    if s.check() != sat:
        raise RuntimeError("No solution found for the given puzzle.")

    m = s.model()

    # Invert mappings to get attribute by house
    house_to_name = {m.evaluate(pos).as_long(): name for name, pos in name_pos.items()}
    house_to_child = {m.evaluate(pos).as_long(): child for child, pos in child_pos.items()}

    # Build rows in house order 1..5
    rows = []
    for h in houses:
        rows.append([str(h), house_to_name[h], house_to_child[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "Children"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))