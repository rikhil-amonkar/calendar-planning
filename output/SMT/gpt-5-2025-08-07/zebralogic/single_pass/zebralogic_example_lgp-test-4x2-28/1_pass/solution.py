import json
from z3 import Solver, Int, And, Or, Distinct, Implies

def solve_puzzle():
    # Indices for names and hair colors
    NAMES = ["Alice", "Arnold", "Peter", "Eric"]
    HAIRS = ["black", "blonde", "brown", "red"]

    # Map names/hairs to integer codes
    name_idx = {name: i for i, name in enumerate(NAMES)}
    hair_idx = {hair: i for i, hair in enumerate(HAIRS)}

    # Variables: for each house (0..3), assign a name and a hair color
    name = [Int(f"name_{i}") for i in range(4)]
    hair = [Int(f"hair_{i}") for i in range(4)]

    s = Solver()

    # Domains
    for i in range(4):
        s.add(name[i] >= 0, name[i] < 4)
        s.add(hair[i] >= 0, hair[i] < 4)

    # Uniqueness
    s.add(Distinct(name))
    s.add(Distinct(hair))

    # Clue 5: Alice is in the first house.
    s.add(name[0] == name_idx["Alice"])

    # Clue 2: Alice and Arnold are next to each other.
    s.add(Or(
        Or(
            And(name[0] == name_idx["Alice"], name[1] == name_idx["Arnold"]),
            And(name[1] == name_idx["Alice"], name[0] == name_idx["Arnold"])
        ),
        Or(
            And(name[1] == name_idx["Alice"], name[2] == name_idx["Arnold"]),
            And(name[2] == name_idx["Alice"], name[1] == name_idx["Arnold"])
        ),
        Or(
            And(name[2] == name_idx["Alice"], name[3] == name_idx["Arnold"]),
            And(name[3] == name_idx["Alice"], name[2] == name_idx["Arnold"])
        )
    ))

    # Clue 3: Eric is the person who has brown hair.
    for i in range(4):
        s.add(Implies(name[i] == name_idx["Eric"], hair[i] == hair_idx["brown"]))
        s.add(Implies(hair[i] == hair_idx["brown"], name[i] == name_idx["Eric"]))

    # Clue 1: Eric is directly left of the person who has blonde hair.
    s.add(Or(
        And(name[0] == name_idx["Eric"], hair[1] == hair_idx["blonde"]),
        And(name[1] == name_idx["Eric"], hair[2] == hair_idx["blonde"]),
        And(name[2] == name_idx["Eric"], hair[3] == hair_idx["blonde"])
    ))

    # Clue 4: The person who has black hair is not in the first house.
    s.add(hair[0] != hair_idx["black"])

    if s.check() != 1:  # 1 == z3.sat
        raise RuntimeError("No solution found")

    m = s.model()

    rows = []
    for i in range(4):
        house_num = str(i + 1)
        name_str = NAMES[m.evaluate(name[i]).as_long()]
        hair_str = HAIRS[m.evaluate(hair[i]).as_long()]
        rows.append([house_num, name_str, hair_str])

    result = {
        "solution": {
            "header": ["House", "Name", "HairColor"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    solve_puzzle()