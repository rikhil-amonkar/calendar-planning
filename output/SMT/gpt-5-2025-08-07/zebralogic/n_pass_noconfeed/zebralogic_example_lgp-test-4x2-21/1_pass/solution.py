import json
from z3 import Solver, Int, And, Or, Distinct

def solve_puzzle():
    # Constants
    houses = [1, 2, 3, 4]
    NAMES = ["Eric", "Arnold", "Alice", "Peter"]
    STYLES = ["craftsman", "colonial", "ranch", "victorian"]

    name_idx = {n: i for i, n in enumerate(NAMES)}
    style_idx = {s: i for i, s in enumerate(STYLES)}

    # Z3 variables: for each house, an index for name and style
    name_vars = [Int(f"name_{h}") for h in houses]
    style_vars = [Int(f"style_{h}") for h in houses]

    s = Solver()

    # Domain constraints
    for v in name_vars + style_vars:
        s.add(v >= 0, v < 4)

    # Uniqueness constraints: each name and style appears exactly once
    s.add(Distinct(name_vars))
    s.add(Distinct(style_vars))

    # Clue 1: Alice is in the second house.
    s.add(name_vars[1] == name_idx["Alice"])

    # Clue 5: The person in a Craftsman-style house is Alice. (bi-implication at each house)
    for i in range(4):
        s.add((style_vars[i] == style_idx["craftsman"]) == (name_vars[i] == name_idx["Alice"]))

    # Clue 2: The person in a Victorian house is directly left of Peter.
    s.add(Or(
        And(style_vars[0] == style_idx["victorian"], name_vars[1] == name_idx["Peter"]),
        And(style_vars[1] == style_idx["victorian"], name_vars[2] == name_idx["Peter"]),
        And(style_vars[2] == style_idx["victorian"], name_vars[3] == name_idx["Peter"])
    ))

    # Clue 3: Peter is somewhere to the right of the person in a ranch-style home.
    s.add(Or(
        And(style_vars[0] == style_idx["ranch"], Or(name_vars[1] == name_idx["Peter"], name_vars[2] == name_idx["Peter"], name_vars[3] == name_idx["Peter"])),
        And(style_vars[1] == style_idx["ranch"], Or(name_vars[2] == name_idx["Peter"], name_vars[3] == name_idx["Peter"])),
        And(style_vars[2] == style_idx["ranch"], name_vars[3] == name_idx["Peter"])
    ))

    # Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house.
    s.add(Or(
        And(style_vars[0] == style_idx["craftsman"], Or(name_vars[1] == name_idx["Arnold"], name_vars[2] == name_idx["Arnold"], name_vars[3] == name_idx["Arnold"])),
        And(style_vars[1] == style_idx["craftsman"], Or(name_vars[2] == name_idx["Arnold"], name_vars[3] == name_idx["Arnold"])),
        And(style_vars[2] == style_idx["craftsman"], name_vars[3] == name_idx["Arnold"])
    ))

    if s.check() != 1:  # z3.sat == 1
        raise Exception("No solution found")

    m = s.model()

    # Build the JSON output
    rows = []
    for i, h in enumerate(houses):
        n = NAMES[m[name_vars[i]].as_long()]
        st = STYLES[m[style_vars[i]].as_long()]
        rows.append([str(h), n, st])

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()