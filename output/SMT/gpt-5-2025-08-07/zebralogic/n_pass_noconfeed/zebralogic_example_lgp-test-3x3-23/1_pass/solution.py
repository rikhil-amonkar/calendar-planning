import json
from z3 import Solver, Int, And, Distinct, Or

def solve_puzzle():
    houses = [1, 2, 3]

    names = ["Peter", "Arnold", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    hobbies = ["cooking", "photography", "gardening"]

    # Create position variables for each attribute: position is the house number 1..3
    name_pos = {n: Int(f"pos_name_{n}") for n in names}
    occ_pos = {o: Int(f"pos_occ_{o}") for o in occupations}
    hobby_pos = {h: Int(f"pos_hobby_{h}") for h in hobbies}

    s = Solver()

    # Domain constraints: each position is in 1..3
    for d in [name_pos, occ_pos, hobby_pos]:
        for v in d.values():
            s.add(And(v >= 1, v <= 3))

    # All-different constraints within each category
    s.add(Distinct([name_pos[n] for n in names]))
    s.add(Distinct([occ_pos[o] for o in occupations]))
    s.add(Distinct([hobby_pos[h] for h in hobbies]))

    # Clue 1: The person who is a doctor and Eric are next to each other.
    s.add(Or(occ_pos["doctor"] - name_pos["Eric"] == 1, name_pos["Eric"] - occ_pos["doctor"] == 1))

    # Clue 2: The person who loves cooking is directly left of the person who is a teacher.
    s.add(hobby_pos["cooking"] + 1 == occ_pos["teacher"])

    # Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
    s.add(occ_pos["doctor"] > hobby_pos["gardening"])

    # Clue 4: The photography enthusiast is the person who is a teacher.
    s.add(hobby_pos["photography"] == occ_pos["teacher"])

    # Clue 5: The person who is an engineer is Peter.
    s.add(occ_pos["engineer"] == name_pos["Peter"])

    if s.check() != 1:  # 1 is z3.sat
        raise RuntimeError("Puzzle is unsatisfiable or unknown.")

    m = s.model()

    # Helper: find the key in a dict whose position equals house h
    def value_at_house(pos_dict, h):
        for k, v in pos_dict.items():
            if m.evaluate(v).as_long() == h:
                return k
        return None

    rows = []
    for h in houses:
        name = value_at_house(name_pos, h)
        occ = value_at_house(occ_pos, h)
        hobby = value_at_house(hobby_pos, h)
        rows.append([str(h), name, occ, hobby])

    output = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Hobby"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()