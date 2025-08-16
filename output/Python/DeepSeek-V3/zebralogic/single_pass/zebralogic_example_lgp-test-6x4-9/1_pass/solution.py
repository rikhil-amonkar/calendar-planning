import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter']
    phones = ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11']
    nationalities = ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit']
    colors = ['blue', 'red', 'yellow', 'green', 'white', 'purple']

    # Generate all possible permutations for each category
    for name_order in permutations(names):
        # Clue 4: Arnold is directly left of Alice
        try:
            alice_pos = name_order.index('Alice')
            if name_order[alice_pos - 1] != 'Arnold':
                continue
        except (ValueError, IndexError):
            continue

        # Clue 1: Carol is not in the third house
        if name_order[2] == 'Carol':
            continue

        # Clue 3: Carol's favorite color is green (handled later)
        # Clue 5: Alice is German (handled later)
        # Clue 10: Bob is in house 5 (from clue 8 and 10)
        if name_order[4] != 'Bob':
            continue

        # Clue 14: Peter is British
        # Clue 13: Peter loves blue
        # Clue 12: Bob (house 5) is left of Peter, so Peter must be in house 6
        if 'Peter' not in name_order[5]:
            continue

        for phone_order in permutations(phones):
            # Clue 8: samsung galaxy s21 is in house 5
            if phone_order[4] != 'samsung galaxy s21':
                continue

            # Clue 15: samsung galaxy s21 is directly left of iphone 13
            if phone_order[5] != 'iphone 13':
                continue

            # Clue 7: huawei p50 is not in house 3
            if phone_order[2] == 'huawei p50':
                continue

            # Clue 6: oneplus 9 user loves purple
            # Clue 16: norwegian loves purple (so oneplus 9 user is norwegian)
            # Handled in nationality and color sections

            for nat_order in permutations(nationalities):
                # Clue 5: Alice is German
                alice_pos = name_order.index('Alice')
                if nat_order[alice_pos] != 'german':
                    continue

                # Clue 14: Peter is brit
                if nat_order[5] != 'brit':
                    continue

                # Clue 2: one house between dane and brit (brit is in 6, so dane is in 4)
                if nat_order[3] != 'dane':
                    continue

                # Clue 11: dane loves yellow
                # Handled in color section

                # Clue 16: norwegian loves purple
                # Handled in color section

                # Clue 17: xiaomi mi 11 user is chinese
                try:
                    xiaomi_pos = phone_order.index('xiaomi mi 11')
                    if nat_order[xiaomi_pos] != 'chinese':
                        continue
                except ValueError:
                    continue

                for color_order in permutations(colors):
                    # Clue 3: Carol's favorite color is green
                    carol_pos = name_order.index('Carol')
                    if color_order[carol_pos] != 'green':
                        continue

                    # Clue 11: dane loves yellow (dane is in house 4)
                    if color_order[3] != 'yellow':
                        continue

                    # Clue 13: Peter loves blue (house 6)
                    if color_order[5] != 'blue':
                        continue

                    # Clue 6: oneplus 9 user loves purple
                    try:
                        oneplus_pos = phone_order.index('oneplus 9')
                        if color_order[oneplus_pos] != 'purple':
                            continue
                        # Clue 16: norwegian loves purple
                        if nat_order[oneplus_pos] != 'norwegian':
                            continue
                    except ValueError:
                        continue

                    # Clue 9: white is right of red
                    red_pos = color_order.index('red')
                    white_pos = color_order.index('white')
                    if white_pos <= red_pos:
                        continue

                    # All constraints satisfied, construct solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
                            "rows": []
                        }
                    }
                    for i in range(6):
                        row = [
                            str(i + 1),
                            name_order[i],
                            phone_order[i],
                            nat_order[i],
                            color_order[i]
                        ]
                        solution["solution"]["rows"].append(row)
                    return solution

    return {"solution": {"header": [], "rows": []}}

# Solve and print the solution
solution = solve_puzzle()
print(json.dumps(solution, indent=2))