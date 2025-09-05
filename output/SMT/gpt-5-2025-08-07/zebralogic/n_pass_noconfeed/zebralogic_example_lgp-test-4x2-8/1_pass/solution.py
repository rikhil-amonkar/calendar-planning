import json
from z3 import Int, Solver, Distinct, Abs, sat

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Peter", "Arnold", "Alice", "Eric"]
    colors = ["yellow", "green", "red", "white"]

    # Create Z3 variables for positions of each name and color
    N = {name: Int(f"pos_name_{name}") for name in names}
    C = {color: Int(f"pos_color_{color}") for color in colors}

    s = Solver()

    # Domain constraints: all positions are between 1 and 4
    for v in list(N.values()) + list(C.values()):
        s.add(v >= 1, v <= 4)

    # All names occupy distinct houses; all colors occupy distinct houses
    s.add(Distinct([N[n] for n in names]))
    s.add(Distinct([C[c] for c in colors]))

    # Clues:
    # 1. The person whose favorite color is green is in the third house.
    s.add(C["green"] == 3)

    # 2. Peter is in the first house.
    s.add(N["Peter"] == 1)

    # 3. There is one house between the person whose favorite color is red and the person who loves yellow.
    s.add(Abs(C["red"] - C["yellow"]) == 2)

    # 4. Arnold is directly left of Eric.
    s.add(N["Arnold"] + 1 == N["Eric"])

    # 5. Eric is the person who loves yellow.
    s.add(N["Eric"] == C["yellow"])

    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Build inverse mappings: house -> name/color
    house_to_name = {}
    for n in names:
        house_to_name[m[N[n]].as_long()] = n

    house_to_color = {}
    for c in colors:
        house_to_color[m[C[c]].as_long()] = c

    # Prepare JSON output
    solution = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": []
        }
    }

    for h in houses:
        row = [str(h), house_to_name[h], house_to_color[h]]
        solution["solution"]["rows"].append(row)

    print(json.dumps(solution, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()