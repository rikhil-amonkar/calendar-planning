import json
from z3 import Solver, Int, And, Or, Distinct, sat

def solve_puzzle():
    houses = [1, 2, 3, 4]

    names = ['Peter', 'Arnold', 'Alice', 'Eric']
    colors = ['yellow', 'green', 'red', 'white']

    # Variables: each name/color is assigned to a house number 1..4
    name_vars = {n: Int(f"{n}_house") for n in names}
    color_vars = {c: Int(f"{c}_house") for c in colors}

    s = Solver()

    # Domains
    for v in name_vars.values():
        s.add(And(v >= 1, v <= 4))
    for v in color_vars.values():
        s.add(And(v >= 1, v <= 4))

    # All-different within each category
    s.add(Distinct(*name_vars.values()))
    s.add(Distinct(*color_vars.values()))

    # Clues:
    # 1. Green is in the third house.
    s.add(color_vars['green'] == 3)

    # 2. Peter is in the first house.
    s.add(name_vars['Peter'] == 1)

    # 3. There is one house between red and yellow.
    s.add(Or(color_vars['red'] - color_vars['yellow'] == 2,
             color_vars['yellow'] - color_vars['red'] == 2))

    # 4. Arnold is directly left of Eric.
    s.add(name_vars['Arnold'] + 1 == name_vars['Eric'])

    # 5. Eric is the person who loves yellow.
    s.add(name_vars['Eric'] == color_vars['yellow'])

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build reverse lookups: house -> name/color
    house_to_name = {m[name_vars[n]].as_long(): n for n in names}
    house_to_color = {m[color_vars[c]].as_long(): c for c in colors}

    rows = []
    for h in houses:
        rows.append([str(h), house_to_name[h], house_to_color[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    solve_puzzle()