import json
from z3 import Solver, Int, And, Or, Distinct, Implies, sat

def solve_puzzle():
    # Enumerations
    names = ["Peter", "Eric", "Arnold"]
    educations = ["bachelor", "associate", "high school"]
    occupations = ["teacher", "doctor", "engineer"]

    # Index helpers
    name_idx = {n: i for i, n in enumerate(names)}
    edu_idx = {e: i for i, e in enumerate(educations)}
    occ_idx = {o: i for i, o in enumerate(occupations)}

    N = 3  # number of houses

    # Variables for each house (0..2 for houses 1..3)
    name_vars = [Int(f"name_{i}") for i in range(N)]
    edu_vars = [Int(f"edu_{i}") for i in range(N)]
    occ_vars = [Int(f"occ_{i}") for i in range(N)]

    s = Solver()

    # Domain constraints
    for i in range(N):
        s.add(And(name_vars[i] >= 0, name_vars[i] < N))
        s.add(And(edu_vars[i] >= 0, edu_vars[i] < N))
        s.add(And(occ_vars[i] >= 0, occ_vars[i] < N))

    # Uniqueness constraints: each attribute is a permutation across houses
    s.add(Distinct(*name_vars))
    s.add(Distinct(*edu_vars))
    s.add(Distinct(*occ_vars))

    # Clue 1: The teacher is directly left of the associate's degree.
    # Houses are 1..3 left to right, so index i is left of i+1.
    s.add(Or(
        And(occ_vars[0] == occ_idx["teacher"], edu_vars[1] == edu_idx["associate"]),
        And(occ_vars[1] == occ_idx["teacher"], edu_vars[2] == edu_idx["associate"])
    ))

    # Clue 2: The person with an associate's degree and Eric are next to each other.
    s.add(Or(
        And(edu_vars[0] == edu_idx["associate"], name_vars[1] == name_idx["Eric"]),
        And(name_vars[0] == name_idx["Eric"], edu_vars[1] == edu_idx["associate"]),
        And(edu_vars[1] == edu_idx["associate"], name_vars[2] == name_idx["Eric"]),
        And(name_vars[1] == name_idx["Eric"], edu_vars[2] == edu_idx["associate"])
    ))

    # Clue 3: Peter is the person with a high school diploma. (equivalence)
    for i in range(N):
        s.add(Implies(name_vars[i] == name_idx["Peter"], edu_vars[i] == edu_idx["high school"]))
        s.add(Implies(edu_vars[i] == edu_idx["high school"], name_vars[i] == name_idx["Peter"]))

    # Clue 4: The doctor is the person with a bachelor's degree. (equivalence)
    for i in range(N):
        s.add(Implies(occ_vars[i] == occ_idx["doctor"], edu_vars[i] == edu_idx["bachelor"]))
        s.add(Implies(edu_vars[i] == edu_idx["bachelor"], occ_vars[i] == occ_idx["doctor"]))

    if s.check() != sat:
        result = {
            "solution": {
                "header": ["House", "Name", "Education", "Occupation"],
                "rows": []
            }
        }
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return

    m = s.model()

    rows = []
    for i in range(N):
        n = names[m[name_vars[i]].as_long()]
        e = educations[m[edu_vars[i]].as_long()]
        o = occupations[m[occ_vars[i]].as_long()]
        rows.append([str(i + 1), n, e, o])

    result = {
        "solution": {
            "header": ["House", "Name", "Education", "Occupation"],
            "rows": rows
        }
    }
    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()