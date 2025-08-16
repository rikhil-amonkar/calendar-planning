import json
from z3 import Solver, Int, And, Or, Distinct, Implies, sat

def solve_puzzle():
    # Indices for attributes
    names = ["Peter", "Arnold", "Eric"]
    occs = ["doctor", "teacher", "engineer"]
    hobbies = ["cooking", "photography", "gardening"]

    name_idx = {v: i for i, v in enumerate(names)}
    occ_idx = {v: i for i, v in enumerate(occs)}
    hobby_idx = {v: i for i, v in enumerate(hobbies)}

    # Houses are indexed 0..2 (left to right). We'll output 1..3 later.
    H = [0, 1, 2]

    # Variables: for each house, which name/occupation/hobby index it has
    name = [Int(f"name_{i}") for i in H]
    occ = [Int(f"occ_{i}") for i in H]
    hobby = [Int(f"hobby_{i}") for i in H]

    s = Solver()

    # Domains
    for v in name + occ + hobby:
        s.add(And(v >= 0, v < 3))

    # Uniqueness across houses
    s.add(Distinct(name))
    s.add(Distinct(occ))
    s.add(Distinct(hobby))

    # Clue 4: The photography enthusiast is the teacher (equivalence)
    for i in H:
        s.add(Implies(hobby[i] == hobby_idx["photography"], occ[i] == occ_idx["teacher"]))
        s.add(Implies(occ[i] == occ_idx["teacher"], hobby[i] == hobby_idx["photography"]))

    # Clue 5: The engineer is Peter (equivalence)
    for i in H:
        s.add(Implies(occ[i] == occ_idx["engineer"], name[i] == name_idx["Peter"]))
        s.add(Implies(name[i] == name_idx["Peter"], occ[i] == occ_idx["engineer"]))

    # Clue 2: Cooking is directly left of the teacher
    s.add(Or(
        And(hobby[0] == hobby_idx["cooking"], occ[1] == occ_idx["teacher"]),
        And(hobby[1] == hobby_idx["cooking"], occ[2] == occ_idx["teacher"])
    ))

    # Clue 3: Doctor is somewhere to the right of gardening
    s.add(Or(
        And(hobby[0] == hobby_idx["gardening"], occ[1] == occ_idx["doctor"]),
        And(hobby[0] == hobby_idx["gardening"], occ[2] == occ_idx["doctor"]),
        And(hobby[1] == hobby_idx["gardening"], occ[2] == occ_idx["doctor"])
    ))

    # Clue 1: The doctor and Eric are next to each other
    s.add(Or(
        And(occ[0] == occ_idx["doctor"], name[1] == name_idx["Eric"]),
        And(occ[1] == occ_idx["doctor"], name[0] == name_idx["Eric"]),
        And(occ[1] == occ_idx["doctor"], name[2] == name_idx["Eric"]),
        And(occ[2] == occ_idx["doctor"], name[1] == name_idx["Eric"])
    ))

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    rows = []
    for i in H:
        rows.append([
            str(i + 1),
            names[m.evaluate(name[i]).as_long()],
            occs[m.evaluate(occ[i]).as_long()],
            hobbies[m.evaluate(hobby[i]).as_long()],
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Hobby"],
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()