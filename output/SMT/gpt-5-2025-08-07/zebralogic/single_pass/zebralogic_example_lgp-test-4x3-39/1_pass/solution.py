import json
from z3 import Solver, Int, Distinct, And

def solve_puzzle():
    houses = [1, 2, 3, 4]

    names = ["Eric", "Alice", "Peter", "Arnold"]
    hair_colors = ["blonde", "black", "red", "brown"]
    sports = ["swimming", "soccer", "basketball", "tennis"]

    # Position variables: each entity maps to a house number (1..4)
    pos_name = {n: Int(f"pos_name_{n}") for n in names}
    pos_hair = {h: Int(f"pos_hair_{h}") for h in hair_colors}
    pos_sport = {s: Int(f"pos_sport_{s}") for s in sports}

    s = Solver()

    # Domain constraints: each variable in 1..4
    for d in [pos_name, pos_hair, pos_sport]:
        for v in d.values():
            s.add(And(v >= 1, v <= 4))

    # Uniqueness within each category
    s.add(Distinct([pos_name[n] for n in names]))
    s.add(Distinct([pos_hair[h] for h in hair_colors]))
    s.add(Distinct([pos_sport[sp] for sp in sports]))

    # Clues:
    # 1. The person who loves soccer is not in the second house.
    s.add(pos_sport["soccer"] != 2)

    # 2. Eric is the person who has blonde hair.
    s.add(pos_name["Eric"] == pos_hair["blonde"])

    # 3. The person who has blonde hair is somewhere to the right of the person who loves basketball.
    s.add(pos_hair["blonde"] > pos_sport["basketball"])

    # 4. The person who has black hair is the person who loves tennis.
    s.add(pos_hair["black"] == pos_sport["tennis"])

    # 5. Arnold is somewhere to the left of the person who has red hair.
    s.add(pos_name["Arnold"] < pos_hair["red"])

    # 6. Alice is the person who loves swimming.
    s.add(pos_name["Alice"] == pos_sport["swimming"])

    # 7. The person who has red hair is directly left of the person who has black hair.
    s.add(pos_hair["red"] + 1 == pos_hair["black"])

    if s.check() != 1:  # 1 == sat
        raise RuntimeError("No solution found")

    m = s.model()

    # Invert position maps to build house -> attribute
    house_to_name = {m[pos_name[n]].as_long(): n for n in names}
    house_to_hair = {m[pos_hair[h]].as_long(): h for h in hair_colors}
    house_to_sport = {m[pos_sport[sp]].as_long(): sp for sp in sports}

    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport"],
            "rows": []
        }
    }

    for h in houses:
        row = [
            str(h),
            house_to_name[h],
            house_to_hair[h],
            house_to_sport[h]
        ]
        result["solution"]["rows"].append(row)

    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))