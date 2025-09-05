import json
from z3 import Int, Solver, Distinct, And

def solve_puzzle():
    houses = [1, 2, 3, 4]

    names = ["Eric", "Arnold", "Peter", "Alice"]
    hairs = ["blonde", "black", "brown", "red"]
    musics = ["pop", "jazz", "rock", "classical"]

    # Create Z3 variables: position (house number) for each attribute value
    pos_name = {n: Int(f"pos_name_{n}") for n in names}
    pos_hair = {h: Int(f"pos_hair_{h}") for h in hairs}
    pos_music = {m: Int(f"pos_music_{m}") for m in musics}

    s = Solver()

    # Domain constraints: all positions are between 1 and 4
    for v in list(pos_name.values()) + list(pos_hair.values()) + list(pos_music.values()):
        s.add(And(v >= 1, v <= 4))

    # Uniqueness within each category (permutation of houses)
    s.add(Distinct(*pos_name.values()))
    s.add(Distinct(*pos_hair.values()))
    s.add(Distinct(*pos_music.values()))

    # Clues:
    # 1. Eric is the person who has red hair.
    s.add(pos_name["Eric"] == pos_hair["red"])

    # 2. The person who loves classical music is directly left of the person who has blonde hair.
    s.add(pos_music["classical"] + 1 == pos_hair["blonde"])

    # 3. The person who has brown hair is not in the first house.
    s.add(pos_hair["brown"] != 1)

    # 4. The person who loves pop music is not in the third house.
    s.add(pos_music["pop"] != 3)

    # 5. The person who loves classical music is in the first house.
    s.add(pos_music["classical"] == 1)

    # 6. The person who loves jazz music is the person who has red hair.
    s.add(pos_music["jazz"] == pos_hair["red"])

    # 7. The person who loves rock music is Arnold.
    s.add(pos_music["rock"] == pos_name["Arnold"])

    # 8. Peter is somewhere to the right of the person who loves rock music.
    s.add(pos_name["Peter"] > pos_music["rock"])

    if s.check() != 1:  # 1 corresponds to sat
        raise RuntimeError("Puzzle has no solution or is not satisfiable.")

    m = s.model()

    # Build reverse lookups: house -> attribute value
    house_to_name = {}
    house_to_hair = {}
    house_to_music = {}

    for n in names:
        house_to_name[m[pos_name[n]].as_long()] = n
    for h in hairs:
        house_to_hair[m[pos_hair[h]].as_long()] = h
    for mu in musics:
        house_to_music[m[pos_music[mu]].as_long()] = mu

    rows = []
    for h in houses:
        rows.append([str(h), house_to_name[h], house_to_hair[h], house_to_music[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "MusicGenre"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False, indent=2))