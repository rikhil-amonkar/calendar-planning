from z3 import Solver, Int, And, Or, Distinct
import json

def solve_puzzle():
    # Domains
    houses = [1, 2, 3]
    Names = ["Eric", "Arnold", "Peter"]
    Heights = ["short", "very short", "average"]

    name_to_id = {n: i for i, n in enumerate(Names)}
    height_to_id = {h: i for i, h in enumerate(Heights)}

    # Z3 variables: for each house (index 0..2), assign a name and a height (as Int IDs)
    name_vars = [Int(f"name_{i+1}") for i in range(3)]
    height_vars = [Int(f"height_{i+1}") for i in range(3)]

    s = Solver()

    # Domain constraints: each variable in 0..2
    for v in name_vars + height_vars:
        s.add(And(v >= 0, v < 3))

    # All names are unique across houses; all heights are unique across houses
    s.add(Distinct(name_vars))
    s.add(Distinct(height_vars))

    # Clue 1: Eric is not in the first house.
    s.add(name_vars[0] != name_to_id["Eric"])

    # Clue 4: Arnold is not in the first house.
    s.add(name_vars[0] != name_to_id["Arnold"])

    # Clue 3: The person who is very short is Eric.
    # For each house j: (height[j] == very short) iff (name[j] == Eric)
    for j in range(3):
        s.add((height_vars[j] == height_to_id["very short"]) == (name_vars[j] == name_to_id["Eric"]))

    # Clue 2: The person who is very short is somewhere to the left of the person who is short.
    # Link positions for "very short" and "short"
    pos_vs = Int("pos_vs")
    pos_s = Int("pos_s")
    s.add(And(pos_vs >= 1, pos_vs <= 3))
    s.add(And(pos_s >= 1, pos_s <= 3))
    s.add(Or(*[And(height_vars[j] == height_to_id["very short"], pos_vs == j + 1) for j in range(3)]))
    s.add(Or(*[And(height_vars[j] == height_to_id["short"], pos_s == j + 1) for j in range(3)]))
    s.add(pos_vs < pos_s)

    # Solve
    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Extract solution per house (1..3)
    rows = []
    for i in range(3):
        house_num = str(i + 1)
        name = Names[m[name_vars[i]].as_long()]
        height = Heights[m[height_vars[i]].as_long()]
        rows.append([house_num, name, height])

    result = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()