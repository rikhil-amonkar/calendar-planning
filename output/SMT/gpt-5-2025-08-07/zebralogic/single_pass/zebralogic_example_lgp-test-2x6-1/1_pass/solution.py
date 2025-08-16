import json
from z3 import Solver, Int, Distinct, And, Or, If, sat

def solve_puzzle():
    # Domains
    names = ["Arnold", "Eric"]
    sports = ["basketball", "soccer"]
    hairs = ["brown", "black"]
    heights = ["very short", "short"]
    smoothies = ["desert", "cherry"]
    flowers = ["daffodils", "carnations"]

    name_idx = {v: i for i, v in enumerate(names)}
    sport_idx = {v: i for i, v in enumerate(sports)}
    hair_idx = {v: i for i, v in enumerate(hairs)}
    height_idx = {v: i for i, v in enumerate(heights)}
    smoothie_idx = {v: i for i, v in enumerate(smoothies)}
    flower_idx = {v: i for i, v in enumerate(flowers)}

    H = 2  # number of houses (indexed 0..1 for z3 variables)
    # Variables per house
    name = [Int(f"name_{i}") for i in range(H)]
    sport = [Int(f"sport_{i}") for i in range(H)]
    hair = [Int(f"hair_{i}") for i in range(H)]
    height = [Int(f"height_{i}") for i in range(H)]
    smoothie = [Int(f"smoothie_{i}") for i in range(H)]
    flower = [Int(f"flower_{i}") for i in range(H)]

    s = Solver()

    # Domain constraints
    for i in range(H):
        s.add(And(name[i] >= 0, name[i] < len(names)))
        s.add(And(sport[i] >= 0, sport[i] < len(sports)))
        s.add(And(hair[i] >= 0, hair[i] < len(hairs)))
        s.add(And(height[i] >= 0, height[i] < len(heights)))
        s.add(And(smoothie[i] >= 0, smoothie[i] < len(smoothies)))
        s.add(And(flower[i] >= 0, flower[i] < len(flowers)))

    # Uniqueness across houses
    s.add(Distinct(name))
    s.add(Distinct(sport))
    s.add(Distinct(hair))
    s.add(Distinct(height))
    s.add(Distinct(smoothie))
    s.add(Distinct(flower))

    # Clue 1: The person who loves soccer is not in the second house.
    s.add(sport[1] != sport_idx["soccer"])

    # Clue 2: The Desert smoothie lover is directly left of the person who is very short.
    # With 2 houses, this implies: house 0 has "desert", house 1 has "very short"
    s.add(smoothie[0] == smoothie_idx["desert"])
    s.add(height[1] == height_idx["very short"])

    # Clue 3: The person who is very short is the person who has brown hair.
    for i in range(H):
        s.add(If(height[i] == height_idx["very short"], hair[i] == hair_idx["brown"], True))
        s.add(If(hair[i] == hair_idx["brown"], height[i] == height_idx["very short"], True))

    # Clue 4: The person who loves a carnations arrangement is the Desert smoothie lover.
    for i in range(H):
        s.add(If(flower[i] == flower_idx["carnations"], smoothie[i] == smoothie_idx["desert"], True))
        s.add(If(smoothie[i] == smoothie_idx["desert"], flower[i] == flower_idx["carnations"], True))

    # Clue 5: Eric and the person who has brown hair are next to each other.
    # With 2 houses, if Eric is in house 0 then brown hair is in house 1, and vice versa.
    s.add(If(name[0] == name_idx["Eric"], hair[1] == hair_idx["brown"], True))
    s.add(If(name[1] == name_idx["Eric"], hair[0] == hair_idx["brown"], True))

    assert s.check() == sat
    m = s.model()

    # Build output JSON
    header = ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"]
    rows = []
    for i in range(H):
        r = [
            str(i + 1),
            names[m[name[i]].as_long()],
            sports[m[sport[i]].as_long()],
            hairs[m[hair[i]].as_long()],
            heights[m[height[i]].as_long()],
            smoothies[m[smoothie[i]].as_long()],
            flowers[m[flower[i]].as_long()],
        ]
        rows.append(r)

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))