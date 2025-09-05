import json
from z3 import *

def main():
    # Enumerations
    names = ["Peter", "Eric", "Alice", "Arnold"]
    educations = ["bachelor", "high school", "associate", "master"]
    music_genres = ["jazz", "rock", "pop", "classical"]
    colors = ["green", "red", "yellow", "white"]
    flowers = ["lilies", "carnations", "daffodils", "roses"]

    name_idx = {v: i for i, v in enumerate(names)}
    edu_idx = {v: i for i, v in enumerate(educations)}
    music_idx = {v: i for i, v in enumerate(music_genres)}
    color_idx = {v: i for i, v in enumerate(colors)}
    flower_idx = {v: i for i, v in enumerate(flowers)}

    # Variables per house (0..3 for houses 1..4)
    H = range(4)
    Name = [Int(f"Name_{i}") for i in H]
    Edu = [Int(f"Edu_{i}") for i in H]
    Music = [Int(f"Music_{i}") for i in H]
    Color = [Int(f"Color_{i}") for i in H]
    Flower = [Int(f"Flower_{i}") for i in H]

    s = Solver()

    # Domain constraints: each var in 0..3
    for arr in [Name, Edu, Music, Color, Flower]:
        for v in arr:
            s.add(And(v >= 0, v <= 3))

    # All-different per attribute
    s.add(Distinct(Name))
    s.add(Distinct(Edu))
    s.add(Distinct(Music))
    s.add(Distinct(Color))
    s.add(Distinct(Flower))

    # Helper for "directly left of": A at i and B at i+1 for some i
    def directly_left_of(A, a_val, B, b_val):
        return Or(*[And(A[i] == a_val, B[i+1] == b_val) for i in range(3)])

    # Clues:
    # 1. bachelor's degree <-> daffodils
    for i in H:
        s.add((Edu[i] == edu_idx["bachelor"]) == (Flower[i] == flower_idx["daffodils"]))

    # 2. carnations not in the first house
    s.add(Flower[0] != flower_idx["carnations"])

    # 3. master's degree is Alice
    for i in H:
        s.add((Edu[i] == edu_idx["master"]) == (Name[i] == name_idx["Alice"]))

    # 4. master's degree directly left of classical music
    s.add(Or(
        And(Edu[0] == edu_idx["master"], Music[1] == music_idx["classical"]),
        And(Edu[1] == edu_idx["master"], Music[2] == music_idx["classical"]),
        And(Edu[2] == edu_idx["master"], Music[3] == music_idx["classical"])
    ))

    # 5. Eric is not in the second house
    s.add(Name[1] != name_idx["Eric"])

    # 6. Arnold is not in the third house
    s.add(Name[2] != name_idx["Arnold"])

    # 7. yellow directly left of roses
    s.add(Or(
        And(Color[0] == color_idx["yellow"], Flower[1] == flower_idx["roses"]),
        And(Color[1] == color_idx["yellow"], Flower[2] == flower_idx["roses"]),
        And(Color[2] == color_idx["yellow"], Flower[3] == flower_idx["roses"])
    ))

    # 8. pop music is in the second house
    s.add(Music[1] == music_idx["pop"])

    # 9. associate's degree is not in the fourth house
    s.add(Edu[3] != edu_idx["associate"])

    # 10. carnations is not in the fourth house
    s.add(Flower[3] != flower_idx["carnations"])

    # 11. red directly left of white
    s.add(Or(
        And(Color[0] == color_idx["red"], Color[1] == color_idx["white"]),
        And(Color[1] == color_idx["red"], Color[2] == color_idx["white"]),
        And(Color[2] == color_idx["red"], Color[3] == color_idx["white"])
    ))

    # 12. red is rock
    for i in H:
        s.add((Color[i] == color_idx["red"]) == (Music[i] == music_idx["rock"]))

    # 13. Arnold is yellow
    for i in H:
        s.add((Name[i] == name_idx["Arnold"]) == (Color[i] == color_idx["yellow"]))

    # 14. daffodils is yellow
    for i in H:
        s.add((Flower[i] == flower_idx["daffodils"]) == (Color[i] == color_idx["yellow"]))

    if s.check() != sat:
        raise RuntimeError("Puzzle constraints are unsatisfiable")

    m = s.model()

    def extract(arr, labels):
        return [labels[m[v].as_long()] for v in arr]

    name_sol = extract(Name, names)
    edu_sol = extract(Edu, educations)
    music_sol = extract(Music, music_genres)
    color_sol = extract(Color, colors)
    flower_sol = extract(Flower, flowers)

    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
            "rows": []
        }
    }

    for i in H:
        row = [
            str(i + 1),
            name_sol[i],
            edu_sol[i],
            music_sol[i],
            color_sol[i],
            flower_sol[i]
        ]
        solution["solution"]["rows"].append(row)

    print(json.dumps(solution, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()