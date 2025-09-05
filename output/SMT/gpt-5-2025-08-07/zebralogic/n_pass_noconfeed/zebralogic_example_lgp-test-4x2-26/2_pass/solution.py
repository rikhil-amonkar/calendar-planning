import json
from z3 import Solver, Int, Distinct, Or, sat

def solve_puzzle():
    houses = [1, 2, 3, 4]

    # Entities
    persons = ["Arnold", "Eric", "Peter", "Alice"]
    occupations = ["doctor", "engineer", "artist", "teacher"]

    # Z3 variables: positions of each person and each occupation
    p_vars = {name: Int(f"pos_{name}") for name in persons}
    o_vars = {occ: Int(f"pos_occ_{occ}") for occ in occupations}

    s = Solver()

    # Domain constraints
    for v in p_vars.values():
        s.add(Or([v == h for h in houses]))
    for v in o_vars.values():
        s.add(Or([v == h for h in houses]))

    # Uniqueness constraints
    s.add(Distinct([p_vars[name] for name in persons]))
    s.add(Distinct([o_vars[occ] for occ in occupations]))

    # Clues:
    # 1. There are two houses between Eric and Peter. (difference of 3)
    s.add(Or(p_vars["Eric"] == p_vars["Peter"] + 3,
             p_vars["Peter"] == p_vars["Eric"] + 3))

    # 2. The person who is a teacher is Peter.
    s.add(o_vars["teacher"] == p_vars["Peter"])

    # 3. Peter is not in the first house.
    s.add(p_vars["Peter"] != 1)

    # 4. There is one house between the person who is a doctor and Alice. (difference of 2)
    s.add(Or(o_vars["doctor"] == p_vars["Alice"] + 2,
             p_vars["Alice"] == o_vars["doctor"] + 2))

    # 5. The person who is an artist is Alice.
    s.add(o_vars["artist"] == p_vars["Alice"])

    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable or unknown.")

    m = s.model()

    # Build mappings from house to attributes
    pos_to_name = {}
    for name in persons:
        pos_to_name[m[p_vars[name]].as_long()] = name

    pos_to_occ = {}
    for occ in occupations:
        pos_to_occ[m[o_vars[occ]].as_long()] = occ

    # Prepare JSON output
    rows = []
    for h in houses:
        rows.append([str(h), pos_to_name[h], pos_to_occ[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "Occupation"],
            "rows": rows
        }
    }

    print(json.dumps(result))

if __name__ == "__main__":
    solve_puzzle()