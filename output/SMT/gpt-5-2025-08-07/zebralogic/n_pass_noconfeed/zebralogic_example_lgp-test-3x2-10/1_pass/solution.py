import json
from z3 import Int, Solver, Distinct, And, Or, sat

def main():
    houses = [1, 2, 3]

    # Define variables: position (house index) of each Name and Height
    name_vars = {
        "Eric": Int("pos_name_Eric"),
        "Arnold": Int("pos_name_Arnold"),
        "Peter": Int("pos_name_Peter"),
    }

    height_vars = {
        "short": Int("pos_height_short"),
        "very short": Int("pos_height_very_short"),
        "average": Int("pos_height_average"),
    }

    s = Solver()

    # Domain constraints: all positions are in {1,2,3}
    for v in list(name_vars.values()) + list(height_vars.values()):
        s.add(And(v >= 1, v <= 3))

    # Uniqueness constraints within each attribute group
    s.add(Distinct(*name_vars.values()))
    s.add(Distinct(*height_vars.values()))

    # Clues:
    # 1. Eric is not in the first house.
    s.add(name_vars["Eric"] != 1)

    # 2. The person who is very short is somewhere to the left of the person who is short.
    s.add(height_vars["very short"] < height_vars["short"])

    # 3. The person who is very short is Eric.
    s.add(height_vars["very short"] == name_vars["Eric"])

    # 4. Arnold is not in the first house.
    s.add(name_vars["Arnold"] != 1)

    if s.check() != sat:
        raise RuntimeError("No solution found for the given puzzle.")

    m = s.model()

    # Build solution rows in house order
    rows = []
    for h in houses:
        # Find the name in house h
        name_in_house = next(n for n, v in name_vars.items() if m.evaluate(v, model_completion=True).as_long() == h)
        # Find the height in house h
        height_in_house = next(ht for ht, v in height_vars.items() if m.evaluate(v, model_completion=True).as_long() == h)
        rows.append([str(h), name_in_house, height_in_house])

    output = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()