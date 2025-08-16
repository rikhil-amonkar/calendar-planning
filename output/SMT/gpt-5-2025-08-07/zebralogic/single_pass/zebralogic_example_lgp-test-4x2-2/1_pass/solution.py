from z3 import Solver, Int, And, Or, Distinct, Implies, sat
import json

def solve():
    # Houses are indexed 0..3 internally (representing houses 1..4)
    houses = range(4)

    # Domains
    names = ["Arnold", "Peter", "Eric", "Alice"]
    styles = ["victorian", "ranch", "colonial", "craftsman"]

    N = {name: i for i, name in enumerate(names)}
    S = {style: i for i, style in enumerate(styles)}
    invN = {i: name for name, i in N.items()}
    invS = {i: style for style, i in S.items()}

    # Variables: name_at_house[i], style_at_house[i] are Int indices into names/styles
    name_at_house = [Int(f"name_{i+1}") for i in houses]
    style_at_house = [Int(f"style_{i+1}") for i in houses]

    s = Solver()

    # Domain constraints
    for i in houses:
        s.add(And(name_at_house[i] >= 0, name_at_house[i] < len(names)))
        s.add(And(style_at_house[i] >= 0, style_at_house[i] < len(styles)))

    # All names and styles are unique across houses
    s.add(Distinct(name_at_house))
    s.add(Distinct(style_at_house))

    # Clue 1: Eric is the person in a Craftsman-style house.
    for i in houses:
        s.add(Implies(name_at_house[i] == N["Eric"], style_at_house[i] == S["craftsman"]))

    # Clue 2: Ranch is directly left of Victorian.
    s.add(Or(
        And(style_at_house[0] == S["ranch"], style_at_house[1] == S["victorian"]),
        And(style_at_house[1] == S["ranch"], style_at_house[2] == S["victorian"]),
        And(style_at_house[2] == S["ranch"], style_at_house[3] == S["victorian"])
    ))

    # Clue 3: Eric is in the third house.
    s.add(name_at_house[2] == N["Eric"])

    # Clue 4: Arnold is in the fourth house.
    s.add(name_at_house[3] == N["Arnold"])

    # Clue 5: The person residing in a Victorian house is Alice.
    for i in houses:
        s.add(Implies(style_at_house[i] == S["victorian"], name_at_house[i] == N["Alice"]))

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    rows = []
    for i in houses:
        name_idx = m[name_at_house[i]].as_long()
        style_idx = m[style_at_house[i]].as_long()
        rows.append([str(i + 1), invN[name_idx], invS[style_idx]])

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }

    print(json.dumps(result))

if __name__ == "__main__":
    solve()