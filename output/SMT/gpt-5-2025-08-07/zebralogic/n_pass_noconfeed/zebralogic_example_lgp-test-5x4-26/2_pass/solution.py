import json
from z3 import Int, Solver, Distinct, And, Or, Abs, sat

def main():
    # Domains
    houses = range(1, 6)

    Names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    Heights = ["very short", "short", "tall", "average", "very tall"]
    Mothers = ["Janelle", "Kailyn", "Penny", "Holly", "Aniya"]
    HairColors = ["blonde", "black", "gray", "red", "brown"]

    # Create position variables: for each attribute value, an Int var for its house position (1..5)
    def make_pos_vars(values, prefix):
        return {v: Int(f"{prefix}_{v.replace(' ', '_')}") for v in values}

    name_pos = make_pos_vars(Names, "NamePos")
    height_pos = make_pos_vars(Heights, "HeightPos")
    mother_pos = make_pos_vars(Mothers, "MotherPos")
    hair_pos = make_pos_vars(HairColors, "HairPos")

    s = Solver()

    # Domain constraints
    for d in [name_pos, height_pos, mother_pos, hair_pos]:
        for v in d.values():
            s.add(And(v >= 1, v <= 5))

    # All-different within each category
    s.add(Distinct([name_pos[n] for n in Names]))
    s.add(Distinct([height_pos[h] for h in Heights]))
    s.add(Distinct([mother_pos[m] for m in Mothers]))
    s.add(Distinct([hair_pos[c] for c in HairColors]))

    # Clues:
    # 1. The person who is tall is The person whose mother's name is Holly.
    s.add(height_pos["tall"] == mother_pos["Holly"])

    # 2. There are two houses between the person who has an average height and the person who is short.
    s.add(Abs(height_pos["average"] - height_pos["short"]) == 3)

    # 3. The person who has gray hair is directly left of The person whose mother's name is Janelle.
    s.add(hair_pos["gray"] + 1 == mother_pos["Janelle"])

    # 4. The person who has black hair is not in the fourth house.
    s.add(hair_pos["black"] != 4)

    # 5. Eric is the person who has black hair.
    s.add(name_pos["Eric"] == hair_pos["black"])

    # 6. The person who is very short is The person whose mother's name is Penny.
    s.add(height_pos["very short"] == mother_pos["Penny"])

    # 7. Eric and the person who has gray hair are next to each other.
    s.add(Abs(name_pos["Eric"] - hair_pos["gray"]) == 1)

    # 8. Bob is in the fifth house.
    s.add(name_pos["Bob"] == 5)

    # 9. The person who has red hair is Peter.
    s.add(hair_pos["red"] == name_pos["Peter"])

    # 10. The person whose mother's name is Kailyn is directly left of the person who is short.
    s.add(mother_pos["Kailyn"] + 1 == height_pos["short"])

    # 11. Arnold is the person who has brown hair.
    s.add(name_pos["Arnold"] == hair_pos["brown"])

    # 12. The person who has brown hair is somewhere to the left of The person whose mother's name is Janelle.
    s.add(hair_pos["brown"] < mother_pos["Janelle"])

    # 13. The person whose mother's name is Aniya and the person who is very short are next to each other.
    s.add(Abs(mother_pos["Aniya"] - height_pos["very short"]) == 1)

    # 14. The person whose mother's name is Kailyn is in the third house.
    s.add(mother_pos["Kailyn"] == 3)

    if s.check() != sat:
        # Fallback JSON in case of unexpected unsat (should not happen for a valid puzzle)
        output = {
            "solution": {
                "header": ["House", "Name", "Height", "Mother", "HairColor"],
                "rows": []
            }
        }
        print(json.dumps(output, ensure_ascii=False))
        return

    m = s.model()

    # Helper to invert position mapping for output
    def value_at_house(pos_dict, house):
        for k, v in pos_dict.items():
            if m.evaluate(v).as_long() == house:
                return k
        return None

    rows = []
    for h in houses:
        name = value_at_house(name_pos, h)
        height = value_at_house(height_pos, h)
        mother = value_at_house(mother_pos, h)
        hair = value_at_house(hair_pos, h)
        rows.append([str(h), name, height, mother, hair])

    output = {
        "solution": {
            "header": ["House", "Name", "Height", "Mother", "HairColor"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()