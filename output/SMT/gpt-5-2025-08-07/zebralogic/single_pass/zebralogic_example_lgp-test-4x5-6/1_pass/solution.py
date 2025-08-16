import json
from z3 import Solver, Int, Distinct, And, Or, sat

def solve_puzzle():
    houses = [1, 2, 3, 4]

    # Domains
    Names = ["Peter", "Eric", "Alice", "Arnold"]
    Educations = ["bachelor", "high school", "associate", "master"]
    MusicGenres = ["jazz", "rock", "pop", "classical"]
    Colors = ["green", "red", "yellow", "white"]
    Flowers = ["lilies", "carnations", "daffodils", "roses"]

    # Create Z3 int variables representing the house number (1..4) for each attribute value
    name_vars = {n: Int(f"name_{n}") for n in Names}
    edu_vars = {e: Int(f"edu_{e.replace(' ', '_')}") for e in Educations}
    music_vars = {m: Int(f"music_{m}") for m in MusicGenres}
    color_vars = {c: Int(f"color_{c}") for c in Colors}
    flower_vars = {f: Int(f"flower_{f}") for f in Flowers}

    s = Solver()

    # All variables in range 1..4
    for var_group in [name_vars, edu_vars, music_vars, color_vars, flower_vars]:
        for v in var_group.values():
            s.add(v >= 1, v <= 4)

    # All-different constraints within each category
    s.add(Distinct([name_vars[n] for n in Names]))
    s.add(Distinct([edu_vars[e] for e in Educations]))
    s.add(Distinct([music_vars[m] for m in MusicGenres]))
    s.add(Distinct([color_vars[c] for c in Colors]))
    s.add(Distinct([flower_vars[f] for f in Flowers]))

    # Clues:
    # 1. The person with a bachelor's degree is the person who loves a bouquet of daffodils.
    s.add(edu_vars["bachelor"] == flower_vars["daffodils"])

    # 2. The person who loves a carnations arrangement is not in the first house.
    s.add(flower_vars["carnations"] != 1)

    # 3. The person with a master's degree is Alice.
    s.add(edu_vars["master"] == name_vars["Alice"])

    # 4. The person with a master's degree is directly left of the person who loves classical music.
    s.add(edu_vars["master"] + 1 == music_vars["classical"])

    # 5. Eric is not in the second house.
    s.add(name_vars["Eric"] != 2)

    # 6. Arnold is not in the third house.
    s.add(name_vars["Arnold"] != 3)

    # 7. The person who loves yellow is directly left of the person who loves the rose bouquet.
    s.add(color_vars["yellow"] + 1 == flower_vars["roses"])

    # 8. The person who loves pop music is in the second house.
    s.add(music_vars["pop"] == 2)

    # 9. The person with an associate's degree is not in the fourth house.
    s.add(edu_vars["associate"] != 4)

    # 10. The person who loves a carnations arrangement is not in the fourth house.
    s.add(flower_vars["carnations"] != 4)

    # 11. The person whose favorite color is red is directly left of the person who loves white.
    s.add(color_vars["red"] + 1 == color_vars["white"])

    # 12. The person whose favorite color is red is the person who loves rock music.
    s.add(color_vars["red"] == music_vars["rock"])

    # 13. Arnold is the person who loves yellow.
    s.add(name_vars["Arnold"] == color_vars["yellow"])

    # 14. The person who loves a bouquet of daffodils is the person who loves yellow.
    s.add(flower_vars["daffodils"] == color_vars["yellow"])

    assert s.check() == sat, "Puzzle is unsatisfiable"
    m = s.model()

    # Helper to invert mapping: given var dict and model, return house->value string
    def invert(var_dict):
        inv = {}
        for label, var in var_dict.items():
            h = m[var].as_long()
            inv[h] = label
        return inv

    inv_names = invert(name_vars)
    inv_edus = invert(edu_vars)
    inv_music = invert(music_vars)
    inv_colors = invert(color_vars)
    inv_flowers = invert(flower_vars)

    rows = []
    for h in houses:
        row = [
            str(h),
            inv_names[h],
            inv_edus[h],
            inv_music[h],
            inv_colors[h],
            inv_flowers[h],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False, indent=2))