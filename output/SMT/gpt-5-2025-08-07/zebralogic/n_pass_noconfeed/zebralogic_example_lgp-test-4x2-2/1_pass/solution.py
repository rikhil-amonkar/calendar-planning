import json
from z3 import Solver, Int, And, Distinct, sat

def solve_puzzle():
    houses = [1, 2, 3, 4]

    # Entities
    names = ["Arnold", "Peter", "Eric", "Alice"]
    styles = ["victorian", "ranch", "colonial", "craftsman"]

    # Variables: position (house index) for each name and style
    name_pos = {n: Int(f"pos_name_{n}") for n in names}
    style_pos = {s: Int(f"pos_style_{s}") for s in styles}

    s = Solver()

    # Domain constraints: positions are within 1..4
    for v in list(name_pos.values()) + list(style_pos.values()):
        s.add(And(v >= 1, v <= 4))

    # Uniqueness: all names in different houses, all styles in different houses
    s.add(Distinct([name_pos[n] for n in names]))
    s.add(Distinct([style_pos[t] for t in styles]))

    # Clue 1: Eric is the person in a Craftsman-style house.
    s.add(name_pos["Eric"] == style_pos["craftsman"])

    # Clue 2: Ranch is directly left of Victorian.
    # Therefore ranch can be at 1..3 and victorian at ranch+1
    s.add(style_pos["ranch"] + 1 == style_pos["victorian"])

    # Clue 3: Eric is in the third house.
    s.add(name_pos["Eric"] == 3)

    # Clue 4: Arnold is in the fourth house.
    s.add(name_pos["Arnold"] == 4)

    # Clue 5: The person residing in a Victorian house is Alice.
    s.add(name_pos["Alice"] == style_pos["victorian"])

    if s.check() != sat:
        # Fallback in the unlikely event of unsat/unknown (should not happen given the clues)
        result = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": [[str(h), "?", "?"] for h in houses]
            }
        }
        return result

    m = s.model()

    # Build reverse lookups for easy house -> attribute mapping
    house_to_name = {m.evaluate(name_pos[n]).as_long(): n for n in names}
    house_to_style = {m.evaluate(style_pos[t]).as_long(): t for t in styles}

    rows = []
    for h in houses:
        rows.append([str(h), house_to_name[h], house_to_style[h]])

    return {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))