import itertools
import json

def solve_zebra():
    names_list = ["Bob", "Eric", "Arnold", "Alice", "Peter"]
    colors_list = ["blue", "green", "white", "yellow", "red"]
    phones_list = ["huawei p50", "samsung galaxy s21", "oneplus 9", "iphone 13", "google pixel 6"]
    occ_list = ["artist", "teacher", "doctor", "engineer", "lawyer"]

    # Go through all possible assignments for houses.
    for names in itertools.permutations(names_list):
        # Constraint 2: Bob is in the second house (index 1)
        if names[1] != "Bob":
            continue

        for occ in itertools.permutations(occ_list):
            valid_occ = True
            # Constraint 10 & 13: Arnold is engineer and Eric is teacher.
            for i in range(5):
                if names[i] == "Eric" and occ[i] != "teacher":
                    valid_occ = False
                    break
                if names[i] == "Arnold" and occ[i] != "engineer":
                    valid_occ = False
                    break
            if not valid_occ:
                continue

            for phones in itertools.permutations(phones_list):
                valid_phone = True
                for i in range(5):
                    # Constraint 12 & 13: The person who uses Google Pixel 6 is Eric and a teacher.
                    if phones[i] == "google pixel 6":
                        if names[i] != "Eric" or occ[i] != "teacher":
                            valid_phone = False
                            break
                    # Constraint 3 & 4: The person who uses a Samsung Galaxy S21 is the doctor who loves blue.
                    if phones[i] == "samsung galaxy s21" and occ[i] != "doctor":
                        valid_phone = False
                        break
                    if occ[i] == "doctor" and phones[i] != "samsung galaxy s21":
                        valid_phone = False
                        break
                    # Constraint 6: The person who is a lawyer uses a OnePlus 9.
                    if occ[i] == "lawyer" and phones[i] != "oneplus 9":
                        valid_phone = False
                        break
                    if phones[i] == "oneplus 9" and occ[i] != "lawyer":
                        valid_phone = False
                        break
                if not valid_phone:
                    continue

                for colors in itertools.permutations(colors_list):
                    valid_color = True
                    for i in range(5):
                        # Constraint 4: The doctor loving blue <=> color must be blue.
                        if occ[i] == "doctor" and colors[i] != "blue":
                            valid_color = False
                            break
                        if colors[i] == "blue" and occ[i] != "doctor":
                            valid_color = False
                            break
                        # Constraint 11: Alice loves yellow.
                        if names[i] == "Alice" and colors[i] != "yellow":
                            valid_color = False
                            break
                    if not valid_color:
                        continue

                    # Constraint 5: The house with number 5 is not green.
                    if colors[4] == "green":
                        continue

                    # Constraint 7: The person who loves blue is directly left of the person whose favorite color is red.
                    blue_red_pair_exists = False
                    for i in range(4):
                        if colors[i] == "blue" and colors[i+1] == "red":
                            blue_red_pair_exists = True
                            break
                    if not blue_red_pair_exists:
                        continue

                    # Constraint 8: The lawyer is somewhere to the right of the person with the Samsung Galaxy S21.
                    try:
                        idx_samsung = phones.index("samsung galaxy s21")
                        idx_lawyer = occ.index("lawyer")
                    except ValueError:
                        continue
                    if idx_lawyer <= idx_samsung:
                        continue

                    # Constraint 1: The engineer is somewhere to the right of the lawyer.
                    try:
                        idx_arnold = names.index("Arnold")
                    except ValueError:
                        continue
                    if idx_arnold <= idx_lawyer:
                        continue

                    # Constraint 9: There is one house between the person who uses Google Pixel 6 and the one who uses Huawei P50.
                    try:
                        idx_pixel = phones.index("google pixel 6")
                        idx_huawei = phones.index("huawei p50")
                    except ValueError:
                        continue
                    if abs(idx_pixel - idx_huawei) != 2:
                        continue

                    # Constraint 14: The person whose favorite color is red is somewhere to the right of the teacher.
                    try:
                        idx_teacher = occ.index("teacher")  # teacher is Eric (by previous constraint)
                        idx_red = colors.index("red")
                    except ValueError:
                        continue
                    if idx_red <= idx_teacher:
                        continue

                    # If all constraints are satisfied, construct the solution.
                    solution = []
                    for i in range(5):
                        # Houses are numbered 1 to 5.
                        solution.append([
                            str(i + 1),
                            names[i],
                            colors[i],
                            phones[i],
                            occ[i]
                        ])
                    return solution
    return None

def main():
    sol = solve_zebra()
    if sol is None:
        result = {
            "solution": {
                "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
                "rows": []
            }
        }
    else:
        result = {
            "solution": {
                "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
                "rows": sol
            }
        }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()