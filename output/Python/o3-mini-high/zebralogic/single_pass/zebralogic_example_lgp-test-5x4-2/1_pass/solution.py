#!/usr/bin/env python3
import itertools
import json

def solve():
    names = ['Bob', 'Eric', 'Arnold', 'Alice', 'Peter']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    phones = ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6']
    occupations = ['artist', 'teacher', 'doctor', 'engineer', 'lawyer']
    
    # Houses are indexed 0 to 4 (House numbers 1 to 5)
    for perm_names in itertools.permutations(names):
        # Clue 2: Bob is in the second house (index 1).
        if perm_names[1] != 'Bob':
            continue

        for perm_colors in itertools.permutations(colors):
            # Clue 11: Alice loves yellow.
            valid_alice = True
            for i in range(5):
                if perm_names[i] == 'Alice' and perm_colors[i] != 'yellow':
                    valid_alice = False
                    break
            if not valid_alice:
                continue
            # Clue 5: Green is not in the fifth house (index 4).
            if perm_colors[4] == 'green':
                continue
            # Clue 7: The person who loves blue is directly left of the person whose favorite color is red.
            blue_left_red = False
            for i in range(4):
                if perm_colors[i] == 'blue' and perm_colors[i+1] == 'red':
                    blue_left_red = True
                    break
            if not blue_left_red:
                continue

            for perm_phones in itertools.permutations(phones):
                # Clue 9: There is one house between the person using Google Pixel 6 and the one using Huawei P50.
                try:
                    idx_pixel = perm_phones.index('google pixel 6')
                    idx_huawei = perm_phones.index('huawei p50')
                except ValueError:
                    continue
                if abs(idx_pixel - idx_huawei) != 2:
                    continue

                for perm_occupations in itertools.permutations(occupations):
                    valid = True
                    houses = range(5)

                    # Clue 3: The person who uses a Samsung Galaxy S21 is the person who is a doctor.
                    for i in houses:
                        if perm_phones[i] == 'samsung galaxy s21' and perm_occupations[i] != 'doctor':
                            valid = False
                            break
                        if perm_occupations[i] == 'doctor' and perm_phones[i] != 'samsung galaxy s21':
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 4: The doctor loves blue.
                    for i in houses:
                        if perm_occupations[i] == 'doctor' and perm_colors[i] != 'blue':
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 6: The lawyer uses a OnePlus 9.
                    for i in houses:
                        if perm_occupations[i] == 'lawyer' and perm_phones[i] != 'oneplus 9':
                            valid = False
                            break
                        if perm_phones[i] == 'oneplus 9' and perm_occupations[i] != 'lawyer':
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 8: The lawyer is somewhere to the right of the person using the Samsung Galaxy S21.
                    try:
                        index_s21 = perm_phones.index('samsung galaxy s21')
                        index_lawyer = perm_occupations.index('lawyer')
                    except ValueError:
                        valid = False
                    if valid and not (index_lawyer > index_s21):
                        valid = False
                    if not valid:
                        continue

                    # Clue 10: Arnold is the engineer.
                    for i in houses:
                        if perm_names[i] == 'Arnold' and perm_occupations[i] != 'engineer':
                            valid = False
                            break
                        if perm_occupations[i] == 'engineer' and perm_names[i] != 'Arnold':
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 12: The person who uses a Google Pixel 6 is Eric.
                    for i in houses:
                        if perm_phones[i] == 'google pixel 6' and perm_names[i] != 'Eric':
                            valid = False
                            break
                        if perm_names[i] == 'Eric' and perm_phones[i] != 'google pixel 6':
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 13: The person who uses a Google Pixel 6 is the teacher.
                    for i in houses:
                        if perm_phones[i] == 'google pixel 6' and perm_occupations[i] != 'teacher':
                            valid = False
                            break
                        if perm_occupations[i] == 'teacher' and perm_phones[i] != 'google pixel 6':
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 14: The person whose favorite color is red is somewhere to the right of the teacher.
                    try:
                        index_teacher = perm_occupations.index('teacher')
                        index_red = perm_colors.index('red')
                    except ValueError:
                        valid = False
                    if valid and not (index_red > index_teacher):
                        valid = False
                    if not valid:
                        continue

                    # Clue 1: The engineer is somewhere to the right of the lawyer.
                    try:
                        index_engineer = perm_occupations.index('engineer')
                        index_lawyer = perm_occupations.index('lawyer')
                    except ValueError:
                        valid = False
                    if valid and not (index_engineer > index_lawyer):
                        valid = False
                    if not valid:
                        continue

                    # All constraints are satisfied; build the solution.
                    sol_rows = []
                    for i in houses:
                        sol_rows.append([str(i+1), perm_names[i], perm_colors[i], perm_phones[i], perm_occupations[i]])
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
                            "rows": sol_rows
                        }
                    }
                    print(json.dumps(solution))
                    return

if __name__ == '__main__':
    solve()