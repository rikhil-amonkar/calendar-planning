import json
from z3 import Solver, Int, Distinct, Or, And, Implies, sat

def solve_puzzle():
    # Domains
    houses = [0, 1]  # 0->House 1, 1->House 2

    names = ["Eric", "Arnold"]
    mothers = ["Aniya", "Holly"]
    cars = ["ford f150", "tesla model 3"]
    heights = ["short", "very short"]

    idx_name = {n: i for i, n in enumerate(names)}
    idx_mother = {m: i for i, m in enumerate(mothers)}
    idx_car = {c: i for i, c in enumerate(cars)}
    idx_height = {h: i for i, h in enumerate(heights)}

    # Variables per house (values are indices into attribute lists)
    Name = [Int(f"Name_{i+1}") for i in houses]
    Mother = [Int(f"Mother_{i+1}") for i in houses]
    Car = [Int(f"Car_{i+1}") for i in houses]
    Height = [Int(f"Height_{i+1}") for i in houses]

    s = Solver()

    # Domain constraints: each variable is 0 or 1
    for arr in (Name, Mother, Car, Height):
        for v in arr:
            s.add(Or(v == 0, v == 1))

    # Uniqueness across houses
    s.add(Distinct(Name))
    s.add(Distinct(Mother))
    s.add(Distinct(Car))
    s.add(Distinct(Height))

    # Clue 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
    for hA in houses:
        for hT in houses:
            s.add(Implies(And(Name[hA] == idx_name["Arnold"], Car[hT] == idx_car["tesla model 3"]), hT > hA))

    # Clue 2: Arnold is the person who is short.
    for h in houses:
        s.add(Implies(Name[h] == idx_name["Arnold"], Height[h] == idx_height["short"]))

    # Clue 3: The person whose mother's name is Holly is in the second house.
    s.add(Mother[1] == idx_mother["Holly"])

    if s.check() != sat:
        raise ValueError("No solution found")

    m = s.model()

    rows = []
    for i in houses:
        row = [
            str(i + 1),
            names[m.evaluate(Name[i]).as_long()],
            mothers[m.evaluate(Mother[i]).as_long()],
            cars[m.evaluate(Car[i]).as_long()],
            heights[m.evaluate(Height[i]).as_long()],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": ["House", "Name", "Mother", "CarModel", "Height"],
            "rows": rows
        }
    }
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()