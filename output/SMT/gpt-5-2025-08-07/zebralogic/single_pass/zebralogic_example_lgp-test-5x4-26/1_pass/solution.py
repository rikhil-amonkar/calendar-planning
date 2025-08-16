import json
from z3 import Solver, Int, Distinct, And, Or, Abs

def solve_puzzle():
    houses = range(1, 6)

    Names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    Heights = ["very short", "short", "tall", "average", "very tall"]
    Mothers = ["Janelle", "Kailyn", "Penny", "Holly", "Aniya"]
    HairColors = ["blonde", "black", "gray", "red", "brown"]

    # Create position variables for each attribute value: 1..5
    name_pos = {n: Int(f"name_{n}") for n in Names}
    height_pos = {h: Int(f"height_{h.replace(' ', '_')}") for h in Heights}
    mother_pos = {m: Int(f"mother_{m}") for m in Mothers}
    hair_pos = {c: Int(f"hair_{c}") for c in HairColors}

    s = Solver()

    # Domain constraints: each position in 1..5
    for d in (name_pos, height_pos, mother_pos, hair_pos):
        for v in d.values():
            s.add(And(v >= 1, v <= 5))

    # All different within each category
    s.add(Distinct(*name_pos.values()))
    s.add(Distinct(*height_pos.values()))
    s.add(Distinct(*mother_pos.values()))
    s.add(Distinct(*hair_pos.values()))

    # Clues encoding:

    # 1. tall == mother Holly
    s.add(height_pos["tall"] == mother_pos["Holly"])

    # 2. average and short are 3 apart (two houses between)
    s.add(Abs(height_pos["average"] - height_pos["short"]) == 3)

    # 3. gray directly left of Janelle
    s.add(hair_pos["gray"] + 1 == mother_pos["Janelle"])

    # 4. black hair not in 4th house
    s.add(hair_pos["black"] != 4)

    # 5. Eric has black hair
    s.add(name_pos["Eric"] == hair_pos["black"])

    # 6. very short == mother Penny
    s.add(height_pos["very short"] == mother_pos["Penny"])

    # 7. Eric and gray are next to each other
    s.add(Abs(name_pos["Eric"] - hair_pos["gray"]) == 1)

    # 8. Bob is in 5th house
    s.add(name_pos["Bob"] == 5)

    # 9. Peter has red hair
    s.add(name_pos["Peter"] == hair_pos["red"])

    # 10. Kailyn directly left of short
    s.add(mother_pos["Kailyn"] + 1 == height_pos["short"])

    # 11. Arnold has brown hair
    s.add(name_pos["Arnold"] == hair_pos["brown"])

    # 12. brown left of Janelle
    s.add(hair_pos["brown"] < mother_pos["Janelle"])

    # 13. Aniya and very short are next to each other
    s.add(Abs(mother_pos["Aniya"] - height_pos["very short"]) == 1)

    # 14. Kailyn is in 3rd house
    s.add(mother_pos["Kailyn"] == 3)

    if s.check() != 1:  # 1 == sat
        raise RuntimeError("No solution found")

    m = s.model()

    # Build inverse mappings: house -> attribute
    inv_name = {m[name_pos[n]].as_long(): n for n in Names}
    inv_height = {m[height_pos[h]].as_long(): h for h in Heights}
    inv_mother = {m[mother_pos[mm]].as_long(): mm for mm in Mothers}
    inv_hair = {m[hair_pos[c]].as_long(): c for c in HairColors}

    rows = []
    for house in houses:
        rows.append([
            str(house),
            inv_name[house],
            inv_height[house],
            inv_mother[house],
            inv_hair[house]
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "Height", "Mother", "HairColor"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution))