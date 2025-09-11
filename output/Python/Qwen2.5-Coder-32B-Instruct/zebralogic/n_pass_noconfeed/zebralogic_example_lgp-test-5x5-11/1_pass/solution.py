import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
    heights = ['average', 'very tall', 'very short', 'short', 'tall']
    cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
    smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
    phones = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(names))
    for name_order in all_permutations:
        if name_order.index('Eric') + 1 != name_order.index('Alice'):
            continue
        if name_order.index('Eric') + 1 != name_order.index('Cherry'):
            continue
        if name_order.index('Bob') == 3:
            continue
        if abs(name_order.index('Eric') - name_order.index('Dragonfruit')) != 2:
            continue
        if name_order[4] != 'Eric':
            continue
        if name_order.index('Desert') >= name_order.index('Lime'):
            continue

        all_permutations_heights = list(itertools.permutations(heights))
        for height_order in all_permutations_heights:
            if height_order[name_order.index('Eric')] != 'very tall':
                continue
            if height_order[name_order.index('Bob')] != 'average':
                continue
            if height_order[name_order.index('Samsung Galaxy S21')] != 'short':
                continue

            all_permutations_cigars = list(itertools.permutations(cigars))
            for cigar_order in all_permutations_cigars:
                if cigar_order[name_order.index('Prince')] != 'Desert':
                    continue
                if cigar_order[name_order.index('Bob')] != 'Dragonfruit':
                    continue
                if cigar_order[name_order.index('Blends')] != 'short':
                    continue
                if cigar_order[name_order.index('Dunhill')] != 'average':
                    continue
                if cigar_order[name_order.index('Bob')] != 'Dunhill':
                    continue

                all_permutations_smoothies = list(itertools.permutations(smoothies))
                for smoothie_order in all_permutations_smoothies:
                    if smoothie_order[name_order.index('Prince')] != 'Desert':
                        continue
                    if smoothie_order[name_order.index('Eric')] != 'Cherry':
                        continue
                    if smoothie_order[name_order.index('Bob')] != 'Dragonfruit':
                        continue

                    all_permutations_phones = list(itertools.permutations(phones))
                    for phone_order in all_permutations_phones:
                        if phone_order.index('iPhone 13') + 1 != phone_order.index('Blue Master'):
                            continue
                        if abs(phone_order.index('iPhone 13') - phone_order.index('OnePlus 9')) != 1:
                            continue
                        if phone_order[name_order.index('Eric')] != 'iPhone 13':
                            continue
                        if phone_order[name_order.index('Arnold')] + 1 != phone_order.index('Huawei P50'):
                            continue
                        if abs(phone_order.index('Very short') - phone_order.index('Arnold')) != 1:
                            continue

                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
                                "rows": []
                            }
                        }

                        for i in range(5):
                            solution["solution"]["rows"].append([
                                str(i + 1),
                                name_order[i],
                                height_order[i],
                                cigar_order[i],
                                smoothie_order[i],
                                phone_order[i]
                            ])

                        return json.dumps(solution, indent=2)

print(solve_puzzle())