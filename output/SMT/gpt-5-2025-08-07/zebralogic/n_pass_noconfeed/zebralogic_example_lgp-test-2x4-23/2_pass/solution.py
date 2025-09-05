import json
import re
from z3 import Int, Solver, And, Distinct, sat

def sanitize(name):
    return re.sub(r'[^A-Za-z0-9_]', '_', name)

def main():
    houses = [1, 2]

    # Attributes
    Names = ["Eric", "Arnold"]
    Mothers = ["Aniya", "Holly"]
    CarModels = ["ford f150", "tesla model 3"]
    Heights = ["short", "very short"]

    # Create Z3 variables mapping each attribute value to a house index (1..2)
    name_vars = {n: Int(sanitize(n)) for n in Names}
    mother_vars = {m: Int(sanitize(m)) for m in Mothers}
    car_vars = {c: Int(sanitize(c)) for c in CarModels}
    height_vars = {h: Int(sanitize(h)) for h in Heights}

    s = Solver()

    # Domain constraints: each variable is a house index 1..2
    for var in list(name_vars.values()) + list(mother_vars.values()) + list(car_vars.values()) + list(height_vars.values()):
        s.add(And(var >= 1, var <= 2))

    # Uniqueness within each category
    s.add(Distinct(*name_vars.values()))
    s.add(Distinct(*mother_vars.values()))
    s.add(Distinct(*car_vars.values()))
    s.add(Distinct(*height_vars.values()))

    # Clues:
    # 1. The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
    s.add(car_vars["tesla model 3"] > name_vars["Arnold"])

    # 2. Arnold is the person who is short.
    s.add(name_vars["Arnold"] == height_vars["short"])

    # 3. The person whose mother's name is Holly is in the second house.
    s.add(mother_vars["Holly"] == 2)

    if s.check() != sat:
        print(json.dumps({"error": "No solution found"}))
        return

    m = s.model()

    # Helper to invert mapping: house -> value for each category
    def invert(mapping):
        inv = {}
        for val, var in mapping.items():
            house_idx = m[var].as_long()
            inv[house_idx] = val
        return inv

    name_by_house = invert(name_vars)
    mother_by_house = invert(mother_vars)
    car_by_house = invert(car_vars)
    height_by_house = invert(height_vars)

    # Build rows in order of houses 1..2
    rows = []
    for h in houses:
        rows.append([
            str(h),
            name_by_house[h],
            mother_by_house[h],
            car_by_house[h],
            height_by_house[h],
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "CarModel", "Height"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()