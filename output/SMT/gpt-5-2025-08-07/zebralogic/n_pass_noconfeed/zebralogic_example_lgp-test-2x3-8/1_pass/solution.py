import json
from z3 import Solver, Int, And, Distinct

def solve_puzzle():
    houses = [1, 2]

    # Attribute values
    Names = ["Arnold", "Eric"]
    Birthdays = ["april", "sept"]
    Mothers = ["Aniya", "Holly"]

    # Position variables for each attribute value
    name_pos = {n: Int(f"name_pos_{n}") for n in Names}
    bday_pos = {b: Int(f"bday_pos_{b}") for b in Birthdays}
    mother_pos = {m: Int(f"mother_pos_{m}") for m in Mothers}

    solver = Solver()

    # Domain constraints: each position within houses range
    for var in list(name_pos.values()) + list(bday_pos.values()) + list(mother_pos.values()):
        solver.add(And(var >= houses[0], var <= houses[-1]))

    # Uniqueness within each category
    solver.add(Distinct(*name_pos.values()))
    solver.add(Distinct(*bday_pos.values()))
    solver.add(Distinct(*mother_pos.values()))

    # Clues:
    # 1. Eric is somewhere to the left of the person whose mother's name is Holly.
    solver.add(name_pos["Eric"] < mother_pos["Holly"])

    # 2. The person whose birthday is in April is in the first house.
    solver.add(bday_pos["april"] == 1)

    if solver.check() != 1:  # sat == 1
        raise RuntimeError("Puzzle is unsatisfiable")

    model = solver.model()

    # Helper to extract the value assigned to each house
    def value_at_house(pos_map, house_idx):
        for k, v in pos_map.items():
            if model[v].as_long() == house_idx:
                return k
        return None

    rows = []
    for h in houses:
        name = value_at_house(name_pos, h)
        bday = value_at_house(bday_pos, h)
        mother = value_at_house(mother_pos, h)
        rows.append([str(h), name, bday, mother])

    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))