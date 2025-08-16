import json
from z3 import Solver, Int, Distinct, And, sat

def solve_puzzle():
    houses = [1, 2]

    # Variables: house position for each name
    name_vars = {
        "Arnold": Int("house_Arnold"),
        "Eric": Int("house_Eric"),
    }

    # Variables: house position for each vacation
    vacation_vars = {
        "beach": Int("house_beach"),
        "mountain": Int("house_mountain"),
    }

    s = Solver()

    # Domain constraints: each variable is a house number between 1 and 2
    for v in list(name_vars.values()) + list(vacation_vars.values()):
        s.add(And(v >= houses[0], v <= houses[-1]))

    # Uniqueness constraints within each category
    s.add(Distinct(*name_vars.values()))
    s.add(Distinct(*vacation_vars.values()))

    # Clue:
    # 1. Arnold is somewhere to the right of the person who loves beach vacations.
    s.add(name_vars["Arnold"] > vacation_vars["beach"])

    if s.check() != sat:
        raise ValueError("No solution found")

    m = s.model()

    # Build mapping from house to name and vacation
    house_to_name = {m[var].as_long(): name for name, var in name_vars.items()}
    house_to_vac = {m[var].as_long(): vac for vac, var in vacation_vars.items()}

    # Prepare JSON output
    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": []
        }
    }

    for h in houses:
        row = [str(h), house_to_name[h], house_to_vac[h]]
        result["solution"]["rows"].append(row)

    print(json.dumps(result))

if __name__ == "__main__":
    solve_puzzle()