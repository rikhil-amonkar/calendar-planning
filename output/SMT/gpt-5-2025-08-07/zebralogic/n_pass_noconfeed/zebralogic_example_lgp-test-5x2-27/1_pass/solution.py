import json
from z3 import Solver, Int, Distinct, And, Or, Abs, sat

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    names = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
    heights = ["very tall", "average", "tall", "very short", "short"]

    # Variables: position of each name and each height (1..5)
    name_pos = {n: Int(f"name_{n}") for n in names}
    height_pos = {h: Int(f"height_{h.replace(' ', '_')}") for h in heights}

    s = Solver()

    # Domain constraints
    for v in name_pos.values():
        s.add(And(v >= 1, v <= 5))
    for v in height_pos.values():
        s.add(And(v >= 1, v <= 5))

    # All-different constraints within each category
    s.add(Distinct([name_pos[n] for n in names]))
    s.add(Distinct([height_pos[h] for h in heights]))

    # Clues:
    # 1. The person who is short is in the second house.
    s.add(height_pos["short"] == 2)

    # 2. Peter is directly left of Bob. (i.e., Peter + 1 = Bob)
    s.add(name_pos["Peter"] + 1 == name_pos["Bob"])

    # 3. Eric is somewhere to the left of Peter.
    s.add(name_pos["Eric"] < name_pos["Peter"])

    # 4. The person who is very tall is directly left of Peter.
    s.add(height_pos["very tall"] + 1 == name_pos["Peter"])

    # 5. Alice is directly left of the person who has an average height.
    s.add(name_pos["Alice"] + 1 == height_pos["average"])

    # 6. The person who is short and the person who is very short are next to each other.
    s.add(Abs(height_pos["short"] - height_pos["very short"]) == 1)

    # 7. The person who has an average height is in the fifth house.
    s.add(height_pos["average"] == 5)

    if s.check() != sat:
        # Fallback in case of unexpected unsat (should not occur)
        result = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": []
            }
        }
        print(json.dumps(result))
        return

    m = s.model()

    # Build reverse mappings: house -> name/height
    name_at = {i: None for i in houses}
    height_at = {i: None for i in houses}

    for n in names:
        pos = m.eval(name_pos[n]).as_long()
        name_at[pos] = n

    for h in heights:
        pos = m.eval(height_pos[h]).as_long()
        height_at[pos] = h

    rows = []
    for i in houses:
        rows.append([str(i), name_at[i], height_at[i]])

    result = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }

    print(json.dumps(result))

if __name__ == "__main__":
    solve_puzzle()