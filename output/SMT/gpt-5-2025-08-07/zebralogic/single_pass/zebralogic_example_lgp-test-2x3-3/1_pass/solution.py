import json
from z3 import Int, Solver, And, Distinct, sat

def solve_puzzle():
    houses = [1, 2]

    names = ["Arnold", "Eric"]
    foods = ["grilled cheese", "pizza"]
    mothers = ["Holly", "Aniya"]

    # Create Z3 integer variables representing the house position of each attribute value
    NamePos = {name: Int(f"Name_{name}_house") for name in names}
    FoodPos = {food: Int(f"Food_{food}_house") for food in foods}
    MotherPos = {mother: Int(f"Mother_{mother}_house") for mother in mothers}

    s = Solver()

    # Domain constraints: each position is within the house range
    for var in list(NamePos.values()) + list(FoodPos.values()) + list(MotherPos.values()):
        s.add(And(var >= houses[0], var <= houses[-1]))

    # Uniqueness constraints within each category
    s.add(Distinct(*NamePos.values()))
    s.add(Distinct(*FoodPos.values()))
    s.add(Distinct(*MotherPos.values()))

    # Clue 1: grilled cheese is directly left of pizza
    s.add(FoodPos["grilled cheese"] + 1 == FoodPos["pizza"])

    # Clue 2: Arnold is not in the second house
    s.add(NamePos["Arnold"] != 2)

    # Clue 3: Arnold is the person whose mother's name is Holly
    s.add(NamePos["Arnold"] == MotherPos["Holly"])

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Invert mappings: house index -> attribute value
    def invert(pos_map):
        result = {}
        for val, var in pos_map.items():
            result[m[var].as_long()] = val
        return result

    name_at = invert(NamePos)
    food_at = invert(FoodPos)
    mother_at = invert(MotherPos)

    rows = []
    for h in houses:
        rows.append([str(h), name_at[h], food_at[h], mother_at[h]])

    output = {
        "solution": {
            "header": ["House", "Name", "Food", "Mother"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()