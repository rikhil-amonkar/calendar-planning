import json
from z3 import Solver, Int, And, Or, Distinct, sat

def solve_puzzle():
    # Constants
    houses = [1, 2]
    n = len(houses)

    NAME = {"Eric": 0, "Arnold": 1}
    RNAME = {v: k for k, v in NAME.items()}

    HOUSESTYLE = {"victorian": 0, "colonial": 1}
    RHOUSESTYLE = {v: k for k, v in HOUSESTYLE.items()}

    HEIGHT = {"very short": 0, "short": 1}
    RHEIGHT = {v: k for k, v in HEIGHT.items()}

    EDUCATION = {"associate": 0, "high school": 1}
    REDUCATION = {v: k for k, v in EDUCATION.items()}

    # Variables per house (index 0 -> house 1, index 1 -> house 2)
    name_vars = [Int(f"name_{h}") for h in houses]
    style_vars = [Int(f"style_{h}") for h in houses]
    height_vars = [Int(f"height_{h}") for h in houses]
    edu_vars = [Int(f"edu_{h}") for h in houses]

    s = Solver()

    # Domain constraints
    for v in name_vars:
        s.add(And(v >= 0, v < len(NAME)))
    for v in style_vars:
        s.add(And(v >= 0, v < len(HOUSESTYLE)))
    for v in height_vars:
        s.add(And(v >= 0, v < len(HEIGHT)))
    for v in edu_vars:
        s.add(And(v >= 0, v < len(EDUCATION)))

    # Uniqueness constraints
    s.add(Distinct(name_vars))
    s.add(Distinct(style_vars))
    s.add(Distinct(height_vars))
    s.add(Distinct(edu_vars))

    # Clue 1: The person who is short is directly left of Eric.
    left_pairs = []
    for i in range(n - 1):
        left_pairs.append(And(height_vars[i] == HEIGHT["short"], name_vars[i + 1] == NAME["Eric"]))
    s.add(Or(left_pairs))

    # Clue 2: The person residing in a Victorian house is in the first house.
    s.add(style_vars[0] == HOUSESTYLE["victorian"])

    # Clue 3: The person who is short is the person with an associate's degree.
    for i in range(n):
        s.add((height_vars[i] == HEIGHT["short"]) == (edu_vars[i] == EDUCATION["associate"]))

    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    rows = []
    for h in houses:
        idx = h - 1
        name_str = RNAME[m[name_vars[idx]].as_long()]
        style_str = RHOUSESTYLE[m[style_vars[idx]].as_long()]
        height_str = RHEIGHT[m[height_vars[idx]].as_long()]
        edu_str = REDUCATION[m[edu_vars[idx]].as_long()]

        rows.append([str(h), name_str, style_str, height_str, edu_str])

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Height", "Education"],
            "rows": rows
        }
    }
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()