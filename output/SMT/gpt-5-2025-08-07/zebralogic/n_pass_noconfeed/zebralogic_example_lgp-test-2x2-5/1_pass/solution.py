import json
from z3 import Solver, Int, Or, And, Distinct, sat

def solve_puzzle():
    # Definitions
    houses = [1, 2]  # left to right
    names = ["Eric", "Arnold"]
    styles = ["victorian", "colonial"]

    num_houses = len(houses)
    name_idx = {name: i for i, name in enumerate(names)}
    style_idx = {style: i for i, style in enumerate(styles)}

    # Z3 variables
    NameVars = [Int(f"Name_{h}") for h in houses]
    StyleVars = [Int(f"HouseStyle_{h}") for h in houses]

    s = Solver()

    # Domain constraints
    for v in NameVars:
        s.add(Or([v == i for i in range(len(names))]))
    for v in StyleVars:
        s.add(Or([v == i for i in range(len(styles))]))

    # All-different constraints per attribute
    s.add(Distinct(NameVars))
    s.add(Distinct(StyleVars))

    # Clue 1: Victorian is somewhere to the left of Colonial
    left_constraints = []
    for i in range(num_houses):
        for j in range(i + 1, num_houses):
            left_constraints.append(
                And(StyleVars[i] == style_idx["victorian"], StyleVars[j] == style_idx["colonial"])
            )
    s.add(Or(left_constraints))

    # Clue 2: Eric is in the first house
    s.add(NameVars[0] == name_idx["Eric"])

    # Solve
    if s.check() != sat:
        raise RuntimeError("No solution found for the given puzzle.")

    m = s.model()

    # Build output
    rows = []
    for i, h in enumerate(houses):
        name_value = names[m.evaluate(NameVars[i]).as_long()]
        style_value = styles[m.evaluate(StyleVars[i]).as_long()]
        rows.append([str(h), name_value, style_value])

    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))