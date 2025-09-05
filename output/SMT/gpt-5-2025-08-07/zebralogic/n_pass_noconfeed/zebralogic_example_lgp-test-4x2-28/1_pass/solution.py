import json
from z3 import Int, Solver, And, Or, Distinct

def solve_puzzle():
    # Enumerations
    NAMES = ["Alice", "Arnold", "Peter", "Eric"]
    HAIRS = ["black", "blonde", "brown", "red"]

    name_to = {n: i for i, n in enumerate(NAMES)}
    hair_to = {h: i for i, h in enumerate(HAIRS)}

    # Variables: for each house (1..4), assign a name and a hair color
    name_vars = [Int(f"name_{i+1}") for i in range(4)]
    hair_vars = [Int(f"hair_{i+1}") for i in range(4)]

    s = Solver()

    # Domains
    for i in range(4):
        s.add(And(name_vars[i] >= 0, name_vars[i] < len(NAMES)))
        s.add(And(hair_vars[i] >= 0, hair_vars[i] < len(HAIRS)))

    # Uniqueness across houses
    s.add(Distinct(name_vars))
    s.add(Distinct(hair_vars))

    # Clue 5: Alice is in the first house.
    s.add(name_vars[0] == name_to["Alice"])

    # Clue 2: Alice and Arnold are next to each other.
    s.add(Or(
        And(name_vars[0] == name_to["Alice"], name_vars[1] == name_to["Arnold"]),
        And(name_vars[1] == name_to["Alice"], Or(name_vars[0] == name_to["Arnold"], name_vars[2] == name_to["Arnold"])),
        And(name_vars[2] == name_to["Alice"], Or(name_vars[1] == name_to["Arnold"], name_vars[3] == name_to["Arnold"])),
        And(name_vars[3] == name_to["Alice"], name_vars[2] == name_to["Arnold"])
    ))

    # Clue 1: Eric is directly left of the person who has blonde hair.
    s.add(Or(
        And(name_vars[0] == name_to["Eric"], hair_vars[1] == hair_to["blonde"]),
        And(name_vars[1] == name_to["Eric"], hair_vars[2] == hair_to["blonde"]),
        And(name_vars[2] == name_to["Eric"], hair_vars[3] == hair_to["blonde"])
    ))

    # Clue 3: Eric is the person who has brown hair.
    s.add(Or(
        And(name_vars[0] == name_to["Eric"], hair_vars[0] == hair_to["brown"]),
        And(name_vars[1] == name_to["Eric"], hair_vars[1] == hair_to["brown"]),
        And(name_vars[2] == name_to["Eric"], hair_vars[2] == hair_to["brown"]),
        And(name_vars[3] == name_to["Eric"], hair_vars[3] == hair_to["brown"])
    ))

    # Clue 4: The person who has black hair is not in the first house.
    s.add(hair_vars[0] != hair_to["black"])

    if s.check() != 1:  # 1 corresponds to sat
        # Fallback JSON structure if unsat/unknown (should not happen with given clues)
        data = {
            "solution": {
                "header": ["House", "Name", "HairColor"],
                "rows": [[str(i+1), "", ""] for i in range(4)]
            }
        }
        print(json.dumps(data))
        return

    m = s.model()

    rows = []
    for i in range(4):
        name_val = NAMES[m[name_vars[i]].as_long()]
        hair_val = HAIRS[m[hair_vars[i]].as_long()]
        rows.append([str(i + 1), name_val, hair_val])

    data = {
        "solution": {
            "header": ["House", "Name", "HairColor"],
            "rows": rows
        }
    }
    print(json.dumps(data))

if __name__ == "__main__":
    solve_puzzle()