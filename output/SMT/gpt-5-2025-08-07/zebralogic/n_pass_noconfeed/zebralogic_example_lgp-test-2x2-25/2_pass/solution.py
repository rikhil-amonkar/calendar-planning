import json
from z3 import Solver, Int, Distinct, And, sat

def solve_puzzle():
    # Houses
    houses = [1, 2]

    # Attributes
    Names = ["Arnold", "Eric"]
    Vacations = ["beach", "mountain"]

    # Z3 variables: position (house number) for each attribute value
    name_pos = {n: Int(f"name_{n}") for n in Names}
    vacation_pos = {v: Int(f"vacation_{v}") for v in Vacations}

    s = Solver()

    # Domain constraints: each attribute value is assigned to a house 1..N
    for v in name_pos.values():
        s.add(And(v >= houses[0], v <= houses[-1]))
    for v in vacation_pos.values():
        s.add(And(v >= houses[0], v <= houses[-1]))

    # Uniqueness within each category
    s.add(Distinct([name_pos[n] for n in Names]))
    s.add(Distinct([vacation_pos[v] for v in Vacations]))

    # Clue:
    # 1. Arnold is somewhere to the right of the person who loves beach vacations.
    s.add(name_pos["Arnold"] > vacation_pos["beach"])

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build solution rows per house in order
    rows = []
    for h in houses:
        # Find which name and vacation are at house h
        name_at_h = next(n for n in Names if m.evaluate(name_pos[n]).as_long() == h)
        vacation_at_h = next(v for v in Vacations if m.evaluate(vacation_pos[v]).as_long() == h)
        rows.append([str(h), name_at_h, vacation_at_h])

    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": rows
        }
    }
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()