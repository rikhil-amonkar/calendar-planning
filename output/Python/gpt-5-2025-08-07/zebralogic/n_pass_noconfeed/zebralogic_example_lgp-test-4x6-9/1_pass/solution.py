import json
from itertools import permutations

def solve():
    houses = [1, 2, 3, 4]

    Names = ["Peter", "Arnold", "Eric", "Alice"]
    Flowers = ["daffodils", "carnations", "roses", "lilies"]
    Heights = ["very short", "short", "tall", "average"]
    Mothers = ["Janelle", "Kailyn", "Holly", "Aniya"]
    Occupations = ["engineer", "doctor", "teacher", "artist"]
    Sports = ["swimming", "basketball", "tennis", "soccer"]

    solution = None

    # Pre-calc all permutations
    name_perms = list(permutations(Names))
    flower_perms = list(permutations(Flowers))
    height_perms = list(permutations(Heights))
    mother_perms = list(permutations(Mothers))
    # For occupations, we know house1 is 'teacher'
    occ_remaining = [o for o in Occupations if o != "teacher"]
    occ_perms_rest = list(permutations(occ_remaining))  # for houses 2..4
    sport_perms = list(permutations(Sports))

    for names in name_perms:
        # C9: Arnold is not in the third house (house index 2 in 0-based)
        if names[2] == "Arnold":
            continue

        # positions for names
        pos_name = {name: names.index(name) for name in Names}

        for flowers in flower_perms:
            # C2: The person who loves the rose bouquet is Eric.
            if flowers.index("roses") != pos_name["Eric"]:
                continue

            # C13: Arnold is the person who loves the boquet of lilies.
            if flowers.index("lilies") != pos_name["Arnold"]:
                continue

            # C7 depends on mothers; C1 depends on sports; C4 depends on occupations later.

            for heights in height_perms:
                pos_height = {h: heights.index(h) for h in Heights}

                # C3: Arnold is tall.
                if pos_height["tall"] != pos_name["Arnold"]:
                    continue

                # C10: Holly somewhere to the right of the person who has an average height -> average can't be at house 4
                if pos_height["average"] == 3:
                    continue

                for mothers in mother_perms:
                    pos_mother = {m: mothers.index(m) for m in Mothers}

                    # C7: Janelle corresponds to carnations
                    if pos_mother["Janelle"] != flowers.index("carnations"):
                        continue

                    # C10: Holly is somewhere to the right of the person who has an average height.
                    if pos_mother["Holly"] <= pos_height["average"]:
                        continue

                    # C12: The person whose mother's name is Aniya is Alice.
                    if pos_mother["Aniya"] != pos_name["Alice"]:
                        continue

                    # Build occupation permutations with house1 fixed as teacher
                    for occ_rest in occ_perms_rest:
                        occupations = ["teacher"] + list(occ_rest)
                        pos_occ = {o: occupations.index(o) for o in Occupations}

                        # C6: teacher in the first house (already enforced by construction)
                        if occupations[0] != "teacher":
                            continue

                        # C11: Peter is the doctor.
                        if pos_occ["doctor"] != pos_name["Peter"]:
                            continue

                        # C4: daffodils is somewhere to the right of engineer.
                        if flowers.index("daffodils") <= pos_occ["engineer"]:
                            continue

                        for sports in sport_perms:
                            pos_sport = {s: sports.index(s) for s in Sports}

                            # C1: The person who loves swimming is the person who loves the rose bouquet.
                            if pos_sport["swimming"] != flowers.index("roses"):
                                continue

                            # C5: The person who loves soccer is the person who is short.
                            if pos_sport["soccer"] != pos_height["short"]:
                                continue

                            # C8: The person who loves basketball is the person who has an average height.
                            if pos_sport["basketball"] != pos_height["average"]:
                                continue

                            # All constraints satisfied
                            solution = []
                            for i in range(4):
                                solution.append({
                                    "House": str(i+1),
                                    "Name": names[i],
                                    "Flower": flowers[i],
                                    "Height": heights[i],
                                    "Mother": mothers[i],
                                    "Occupation": occupations[i],
                                    "FavoriteSport": sports[i],
                                })
                            # We can return the first solution found
                            return solution
    return None

def main():
    solved = solve()
    if not solved:
        output = {
            "solution": {
                "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                "rows": []
            }
        }
    else:
        rows = []
        for row in solved:
            rows.append([
                row["House"],
                row["Name"],
                row["Flower"],
                row["Height"],
                row["Mother"],
                row["Occupation"],
                row["FavoriteSport"],
            ])
        output = {
            "solution": {
                "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                "rows": rows
            }
        }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()