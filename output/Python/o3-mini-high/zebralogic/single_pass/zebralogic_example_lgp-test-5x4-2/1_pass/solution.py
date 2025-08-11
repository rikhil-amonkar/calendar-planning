#!/usr/bin/env python3
import itertools
import json
import sys

def main():
    # Define the possible attributes
    names_all = ["Bob", "Eric", "Arnold", "Alice", "Peter"]
    colors_all = ["blue", "green", "white", "yellow", "red"]
    phones_all = ["huawei p50", "samsung galaxy s21", "oneplus 9", "iphone 13", "google pixel 6"]
    occupations_all = ["artist", "teacher", "doctor", "engineer", "lawyer"]

    solution = None

    # Iterate over valid permutations for names.
    # Clue 2: Bob is in the second house (index 1)
    for names in itertools.permutations(names_all):
        if names[1] != "Bob":
            continue

        # Iterate over occupations satisfying clues:
        # Clue 10: Arnold is the engineer.
        # Clue 12 & 13: Eric is the teacher.
        for occs in itertools.permutations(occupations_all):
            valid_occ = True
            for i in range(5):
                if names[i] == "Eric" and occs[i] != "teacher":
                    valid_occ = False
                    break
                if names[i] == "Arnold" and occs[i] != "engineer":
                    valid_occ = False
                    break
            if not valid_occ:
                continue
            # Clue 1: The engineer is somewhere to the right of the lawyer.
            try:
                idx_engineer = occs.index("engineer")
                idx_lawyer = occs.index("lawyer")
            except ValueError:
                continue
            if idx_engineer <= idx_lawyer:
                continue

            # Iterate over color permutations.
            for colors in itertools.permutations(colors_all):
                valid_color = True
                for i in range(5):
                    # Clue 11: Alice is the person who loves yellow.
                    if names[i] == "Alice" and colors[i] != "yellow":
                        valid_color = False
                        break
                    # Clue 4: The doctor is the person who loves blue.
                    if occs[i] == "doctor" and colors[i] != "blue":
                        valid_color = False
                        break
                if not valid_color:
                    continue
                # Clue 5: The person whose favorite color is green is not in the fifth house.
                if colors[4] == "green":
                    continue
                # Clue 7: The person who loves blue is directly left of the person whose favorite color is red.
                try:
                    blue_index = colors.index("blue")
                    if blue_index == 4 or colors[blue_index+1] != "red":
                        continue
                except ValueError:
                    continue
                # Clue 14: The person whose favorite color is red is somewhere to the right of the person who is a teacher.
                try:
                    teacher_index = occs.index("teacher")
                    red_index = colors.index("red")
                    if teacher_index >= red_index:
                        continue
                except ValueError:
                    continue

                # Iterate over phone permutations.
                for phones in itertools.permutations(phones_all):
                    valid_phone = True
                    for i in range(5):
                        # Clue 12: The person who uses a Google Pixel 6 is Eric.
                        if names[i] == "Eric" and phones[i] != "google pixel 6":
                            valid_phone = False
                            break
                        # Clue 3: The person who uses a Samsung Galaxy S21 is the doctor.
                        if occs[i] == "doctor" and phones[i] != "samsung galaxy s21":
                            valid_phone = False
                            break
                        # Clue 6: The person who is a lawyer is the person who uses a OnePlus 9.
                        if occs[i] == "lawyer" and phones[i] != "oneplus 9":
                            valid_phone = False
                            break
                    if not valid_phone:
                        continue
                    # Clue 8: The person who is a lawyer is somewhere to the right of the person who uses a Samsung Galaxy S21.
                    try:
                        idx_samsung = phones.index("samsung galaxy s21")
                        idx_lawyer_phone = occs.index("lawyer")
                    except ValueError:
                        continue
                    if idx_lawyer_phone <= idx_samsung:
                        continue
                    # Clue 9: There is one house between the person who uses a Google Pixel 6 and the person who uses a Huawei P50.
                    try:
                        idx_pixel = phones.index("google pixel 6")
                        idx_huawei = phones.index("huawei p50")
                    except ValueError:
                        continue
                    if abs(idx_pixel - idx_huawei) != 2:
                        continue
                    # Clue 1 (again): Engineer is to the right of lawyer (already checked above) is still valid.
                    # All clues satisfied? Set solution.
                    solution = []
                    for i in range(5):
                        house = {
                            "House": str(i+1),
                            "Name": names[i],
                            "favorite color": colors[i],
                            "phone models": phones[i],
                            "occupation": occs[i]
                        }
                        solution.append(house)
                    # Since we found a valid solution, break out of loops.
                    break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    # Prepare the JSON output with the required structure.
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "favorite color", "phone models", "occupation"], "rows": []}}
    else:
        # Build rows preserving the order of houses 1 to 5.
        rows = []
        for house in solution:
            row = [house["House"], house["Name"], house["favorite color"], house["phone models"], house["occupation"]]
            rows.append(row)
        output = {"solution": {"header": ["House", "Name", "favorite color", "phone models", "occupation"], "rows": rows}}
    
    # Output the result as JSON.
    json_output = json.dumps(output, indent=2)
    sys.stdout.write(json_output)

if __name__ == "__main__":
    main()