import json
import itertools

def solve_puzzle():
    houses = range(5)  # 0..4 represent houses 1..5

    Names = ["Bob", "Eric", "Arnold", "Alice", "Peter"]
    Colors = ["blue", "green", "white", "yellow", "red"]
    Phones = ["huawei p50", "samsung galaxy s21", "oneplus 9", "iphone 13", "google pixel 6"]
    Occupations = ["artist", "teacher", "doctor", "engineer", "lawyer"]

    # Fixed facts:
    # - Bob is in second house (index 1).
    # - Arnold is engineer.
    # - Eric uses Google Pixel 6 and is Teacher.
    # - Doctor uses Samsung Galaxy S21 and likes blue.
    # - Lawyer uses OnePlus 9.
    # - Blue is immediately left of Red.
    # - Red is somewhere to the right of Teacher (Eric).
    # - Green is not in the fifth house (index 4).
    # - Pixel 6 and Huawei P50 are separated by exactly one house (distance 2).

    solutions = []

    # Generate name placements with Bob fixed at house 2 (index 1).
    remaining_names = ["Eric", "Arnold", "Alice", "Peter"]
    for perm in itertools.permutations(remaining_names):
        names_by_house = [None]*5
        names_by_house[1] = "Bob"
        idxs = [0,2,3,4]
        for i, h in enumerate(idxs):
            names_by_house[h] = perm[i]

        # Build reverse lookup for name positions
        pos = {name: names_by_house.index(name) for name in Names}

        # Occupations fixed by names:
        pos_engineer = pos["Arnold"]  # Arnold is engineer.
        pos_teacher = pos["Eric"]     # Eric is teacher.

        # Iterate possible positions for Doctor and Lawyer with order: Doctor < Lawyer < Engineer
        for pos_doc in range(0, 4):  # doctor must have a right neighbor for Red
            if pos_doc == pos_teacher:
                continue  # teacher != doctor
            if not (pos_doc < pos_engineer):  # doctor must be left of engineer
                continue

            # Red must be to the right of Teacher
            if not (pos_doc + 1 > pos_teacher):
                continue

            for pos_lawyer in range(pos_doc + 1, pos_engineer):
                if pos_lawyer == pos_teacher:
                    continue
                # Occupations are unique
                if len({pos_doc, pos_lawyer, pos_engineer, pos_teacher}) < 4:
                    continue

                # Colors: doctor=blue, red right of doctor, Alice=yellow
                colors_by_house = [None]*5
                colors_by_house[pos_doc] = "blue"
                colors_by_house[pos_doc + 1] = "red"
                # Alice is yellow
                colors_by_house[pos["Alice"]] = "yellow"

                # Check no color conflicts so far
                if len([c for c in colors_by_house if c is not None]) != len(set([c for c in colors_by_house if c is not None])):
                    continue

                # Green not in fifth house
                if colors_by_house[4] == "green":
                    continue

                # Phones: Eric=Pixel, Doctor=S21, Lawyer=OnePlus, Pixel and Huawei distance 2
                phones_by_house = [None]*5
                phones_by_house[pos_teacher] = "google pixel 6"
                phones_by_house[pos_doc] = "samsung galaxy s21"
                phones_by_house[pos_lawyer] = "oneplus 9"

                # Determine possible Huawei positions (distance 2 from Pixel)
                pixel_pos = pos_teacher
                huawei_candidates = []
                for d in (-2, 2):
                    hp = pixel_pos + d
                    if 0 <= hp < 5:
                        huawei_candidates.append(hp)

                for pos_huawei in huawei_candidates:
                    if phones_by_house[pos_huawei] is not None:
                        continue  # cannot overlap with existing phone
                    # Assign Huawei
                    phones_by_house_try = phones_by_house[:]
                    phones_by_house_try[pos_huawei] = "huawei p50"

                    # Fill remaining phone with iPhone 13
                    remaining_phone_houses = [i for i, p in enumerate(phones_by_house_try) if p is None]
                    if len(remaining_phone_houses) != 1:
                        continue
                    phones_by_house_try[remaining_phone_houses[0]] = "iphone 13"

                    # Now assign remaining colors (green and white) to unfilled houses
                    filled_colors = [c for c in colors_by_house if c is not None]
                    # Colors used so far: blue, red, yellow assigned already
                    # Remaining: green and white
                    remaining_color_houses = [i for i, c in enumerate(colors_by_house) if c is None]
                    if len(remaining_color_houses) != 2:
                        continue
                    for rc_perm in itertools.permutations(["green", "white"]):
                        colors_try = colors_by_house[:]
                        colors_try[remaining_color_houses[0]] = rc_perm[0]
                        colors_try[remaining_color_houses[1]] = rc_perm[1]
                        # Green not in fifth house
                        if colors_try[4] == "green":
                            continue

                        # Occupations per house
                        occ_by_house = [None]*5
                        occ_by_house[pos_teacher] = "teacher"
                        occ_by_house[pos_doc] = "doctor"
                        occ_by_house[pos_lawyer] = "lawyer"
                        occ_by_house[pos_engineer] = "engineer"
                        # Remaining is artist
                        remaining_occ_house = [i for i, o in enumerate(occ_by_house) if o is None]
                        if len(remaining_occ_house) != 1:
                            continue
                        occ_by_house[remaining_occ_house[0]] = "artist"

                        # Final validation of all constraints:
                        # 1. Engineer right of Lawyer
                        if not (pos_engineer > pos_lawyer):
                            continue
                        # 7. Blue directly left of Red already set (pos_doc and pos_doc+1)
                        # 8. Lawyer right of Samsung (Doctor)
                        if not (pos_lawyer > pos_doc):
                            continue
                        # 9. One house between Pixel and Huawei (distance 2) ensured by selection
                        if abs(pos_huawei - pixel_pos) != 2:
                            continue
                        # 5. Green not fifth ensured
                        # 11. Alice yellow ensured
                        # 12. Pixel is Eric ensured
                        # 13. Pixel is Teacher ensured
                        # 14. Red to right of Teacher ensured earlier

                        # All constraints satisfied, record solution
                        solution = []
                        for h in houses:
                            solution.append({
                                "House": str(h + 1),
                                "Name": names_by_house[h],
                                "Color": colors_try[h],
                                "PhoneModel": phones_by_house_try[h],
                                "Occupation": occ_by_house[h],
                            })
                        solutions.append(solution)

    # Deduplicate solutions in case of symmetric generation
    unique_solutions = []
    seen = set()
    for sol in solutions:
        key = tuple((row["Name"], row["Color"], row["PhoneModel"], row["Occupation"]) for row in sol)
        if key not in seen:
            seen.add(key)
            unique_solutions.append(sol)

    # Choose the first unique solution (should be exactly one for a well-posed puzzle)
    if not unique_solutions:
        raise RuntimeError("No solution found")
    final_sol = unique_solutions[0]

    # Format output as requested
    header = ["House", "Name", "Color", "PhoneModel", "Occupation"]
    rows = []
    for row in final_sol:
        rows.append([row["House"], row["Name"], row["Color"], row["PhoneModel"], row["Occupation"]])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))