import itertools
import json

def main():
    names_list = ['Bob', 'Eric', 'Arnold', 'Alice', 'Peter']
    colors_list = ['blue', 'green', 'white', 'yellow', 'red']
    phones_list = ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6']
    occupations_list = ['artist', 'teacher', 'doctor', 'engineer', 'lawyer']

    # Generate all name permutations where Bob is in house 2 (index 1)
    name_perms = [p for p in itertools.permutations(names_list) if p[1] == 'Bob']

    for names in name_perms:
        e_idx = names.index('Eric')
        a_idx = names.index('Arnold')
        ai_idx = names.index('Alice')

        # Generate all phone permutations where Eric's phone is Google Pixel 6
        phone_perms = itertools.permutations(phones_list)
        for phones in phone_perms:
            if phones[e_idx] != 'google pixel 6':
                continue

            # Generate all color permutations where Alice's color is yellow
            color_perms = itertools.permutations(colors_list)
            for colors in color_perms:
                if colors[ai_idx] != 'yellow':
                    continue

                # Generate all occupation permutations where Eric is teacher and Arnold is engineer
                occ_perms = itertools.permutations(occupations_list)
                for occupations in occ_perms:
                    if occupations[e_idx] != 'teacher' or occupations[a_idx] != 'engineer':
                        continue

                    # Check clue 3 and 4: Samsung user is doctor and loves blue
                    s_idx = None
                    for i in range(5):
                        if phones[i] == 'samsung galaxy s21':
                            s_idx = i
                            break
                    if s_idx is None:
                        continue
                    if occupations[s_idx] != 'doctor' or colors[s_idx] != 'blue':
                        continue

                    # Check clue 6: Lawyer uses oneplus 9
                    lawyer_idx = None
                    for i in range(5):
                        if occupations[i] == 'lawyer':
                            lawyer_idx = i
                            break
                    if lawyer_idx is None:
                        continue
                    if phones[lawyer_idx] != 'oneplus 9':
                        continue

                    # Check clue 5: Green not in house 5
                    if colors[4] == 'green':
                        continue

                    # Check clue 7: Blue directly left of red
                    blue_idx = colors.index('blue')
                    if blue_idx + 1 >= 5 or colors[blue_idx + 1] != 'red':
                        continue

                    # Check clue 8: Lawyer is to the right of Samsung
                    if lawyer_idx <= s_idx:
                        continue

                    # Check clue 9: One house between Google Pixel 6 and Huawei P50
                    huawei_idx = None
                    for i in range(5):
                        if phones[i] == 'huawei p50':
                            huawei_idx = i
                            break
                    if huawei_idx is None:
                        continue
                    if abs(e_idx - huawei_idx) != 2:
                        continue

                    # Check clue 14: Red is to the right of teacher (teacher is at e_idx)
                    red_idx = colors.index('red')
                    if red_idx <= e_idx:
                        continue

                    # Check clue 1: Engineer (a_idx) is to the right of lawyer (lawyer_idx)
                    if a_idx <= lawyer_idx:
                        continue

                    # All constraints satisfied, build the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
                            "rows": []
                        }
                    }
                    for i in range(5):
                        house_num = str(i + 1)
                        name = names[i]
                        color = colors[i]
                        phone = phones[i]
                        occupation = occupations[i]
                        solution["solution"]["rows"].append([house_num, name, color, phone, occupation])

                    print(json.dumps(solution))
                    return

    # If no solution found
    print(json.dumps({"solution": {"header": [], "rows": []}}))

if __name__ == "__main__":
    main()