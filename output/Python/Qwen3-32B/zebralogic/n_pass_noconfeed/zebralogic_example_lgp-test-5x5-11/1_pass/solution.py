import itertools
import json

def solve_puzzle():
    names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
    heights = ['average', 'very tall', 'very short', 'short', 'tall']
    cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
    smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
    phones = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']

    for name_p in itertools.permutations(names):
        e_pos = None
        b_pos = None
        for i in range(5):
            if name_p[i] == 'Eric':
                e_pos = i + 1
            if name_p[i] == 'Bob':
                b_pos = i + 1
        if e_pos is None or b_pos is None:
            continue
        if abs(e_pos - b_pos) != 3:
            continue
        if b_pos == 4:
            continue
        if e_pos + 1 > 5:
            continue

        for height_p in itertools.permutations(heights):
            bob_idx = name_p.index('Bob')
            eric_idx = name_p.index('Eric')
            if height_p[bob_idx] != 'average' or height_p[eric_idx] != 'very tall':
                continue

            for cigar_p in itertools.permutations(cigars):
                if cigar_p[bob_idx] != 'dunhill':
                    continue

                for smoothie_p in itertools.permutations(smoothies):
                    if smoothie_p[bob_idx] != 'dragonfruit':
                        continue

                    for phone_p in itertools.permutations(phones):
                        if phone_p[eric_idx] != 'iphone 13':
                            continue

                        houses = []
                        for i in range(5):
                            house = {
                                'Name': name_p[i],
                                'Height': height_p[i],
                                'Cigar': cigar_p[i],
                                'Smoothie': smoothie_p[i],
                                'PhoneModel': phone_p[i]
                            }
                            houses.append(house)

                        a_pos = None
                        for i in range(5):
                            if name_p[i] == 'Alice':
                                a_pos = i + 1
                                break
                        if abs(e_pos - a_pos) != 2:
                            continue

                        valid = True
                        for i in range(5):
                            if height_p[i] == 'short' and cigar_p[i] != 'blends':
                                valid = False
                                break
                        if not valid:
                            continue

                        eric_house_idx = name_p.index('Eric')
                        if eric_house_idx + 1 >= 5 or cigar_p[eric_house_idx + 1] != 'blue master':
                            continue

                        found_arnold = False
                        for i in range(5):
                            if name_p[i] == 'Arnold':
                                if i + 1 >= 5 or phone_p[i + 1] != 'huawei p50':
                                    found_arnold = False
                                    break
                                found_arnold = True
                        if not found_arnold:
                            continue

                        if smoothie_p[eric_house_idx + 1] != 'cherry':
                            continue

                        eric_phone_idx = name_p.index('Eric')
                        if not ((eric_phone_idx > 0 and phone_p[eric_phone_idx - 1] == 'oneplus 9') or
                                (eric_phone_idx < 4 and phone_p[eric_phone_idx + 1] == 'oneplus 9')):
                            continue

                        for i in range(5):
                            if phone_p[i] == 'samsung galaxy s21' and height_p[i] != 'short':
                                valid = False
                                break
                        if not valid:
                            continue

                        desert_pos = None
                        lime_pos = None
                        for i in range(5):
                            if smoothie_p[i] == 'desert':
                                desert_pos = i
                            if smoothie_p[i] == 'lime':
                                lime_pos = i
                        if desert_pos is not None and lime_pos is not None and desert_pos >= lime_pos:
                            continue

                        found_arnold_short = False
                        for i in range(5):
                            if name_p[i] == 'Arnold':
                                if (i > 0 and height_p[i - 1] == 'very short') or (i < 4 and height_p[i + 1] == 'very short'):
                                    found_arnold_short = True
                                    break
                        if not found_arnold_short:
                            continue

                        prince_smoker = None
                        desert_lover = None
                        for i in range(5):
                            if cigar_p[i] == 'prince':
                                prince_smoker = i
                            if smoothie_p[i] == 'desert':
                                desert_lover = i
                        if prince_smoker is not None and desert_lover is not None:
                            if prince_smoker != desert_lover:
                                continue
                        elif prince_smoker is not None or desert_lover is not None:
                            continue

                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
                                "rows": []
                            }
                        }
                        for i in range(5):
                            row = [
                                str(i + 1),
                                houses[i]['Name'],
                                houses[i]['Height'],
                                houses[i]['Cigar'],
                                houses[i]['Smoothie'],
                                houses[i]['PhoneModel']
                            ]
                            solution["solution"]["rows"].append(row)
                        return json.dumps(solution, indent=2)

    return json.dumps({"solution": {"header": [], "rows": []}})

if __name__ == "__main__":
    result = solve_puzzle()
    print(result)