from z3 import Solver, Int, And, Distinct, If, sat
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Eric", "Arnold", "Alice", "Peter"]
    styles = ["craftsman", "colonial", "ranch", "victorian"]

    # Variables: position (house number) for each name and each style
    pos_name = {n: Int(f"pos_name_{n}") for n in names}
    pos_style = {s: Int(f"pos_style_{s}") for s in styles}

    s = Solver()

    # Domain constraints: each position is between 1 and 4
    for v in list(pos_name.values()) + list(pos_style.values()):
        s.add(And(v >= 1, v <= 4))

    # Uniqueness constraints
    s.add(Distinct([pos_name[n] for n in names]))
    s.add(Distinct([pos_style[st] for st in styles]))

    # Clues:
    # 1. Alice is in the second house.
    s.add(pos_name["Alice"] == 2)

    # 2. The person residing in a Victorian house is directly left of Peter.
    s.add(pos_style["victorian"] + 1 == pos_name["Peter"])

    # 3. Peter is somewhere to the right of the person in a ranch-style home.
    s.add(pos_name["Peter"] > pos_style["ranch"])

    # 4. Arnold is somewhere to the right of the person in a Craftsman-style house.
    s.add(pos_name["Arnold"] > pos_style["craftsman"])

    # 5. The person in a Craftsman-style house is Alice.
    s.add(pos_style["craftsman"] == pos_name["Alice"])

    # Solve
    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build solution rows ordered by house number
    rows = []
    for h in houses:
        # Find the name at house h
        name_at_h = next(n for n in names if m.evaluate(pos_name[n]).as_long() == h)
        # Find the style at house h
        style_at_h = next(st for st in styles if m.evaluate(pos_style[st]).as_long() == h)
        rows.append([str(h), name_at_h, style_at_h])

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()