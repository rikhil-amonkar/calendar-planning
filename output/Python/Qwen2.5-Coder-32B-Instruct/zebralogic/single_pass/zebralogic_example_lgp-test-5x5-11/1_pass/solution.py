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
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(heights)) * \
                       list(itertools.permutations(cigars)) * \
                       list(itertools.permutations(smoothies)) * \
                       list(itertools.permutations(phones))

    def is_valid_solution(permutation):
        name_order, height_order, cigar_order, smoothie_order, phone_order = permutation

        # Unpack the permutation into a list of dictionaries for easier access
        people = [{'house': h + 1, 'name': name_order[h], 'height': height_order[h],
                   'cigar': cigar_order[h], 'smoothie': smoothie_order[h], 'phone': phone_order[h]}
                  for h in range(5)]

        # Apply all clues
        if not any(p['cigar'] == 'prince' and p['smoothie'] == 'desert' for p in people):
            return False
        if abs(name_order.index('Eric') - name_order.index('Alice')) != 2:
            return False
        if not any(p['height'] == 'short' and p['cigar'] == 'blends' for p in people):
            return False
        if not any(people[i]['phone'] == 'iphone 13' and people[i + 1]['cigar'] == 'blue master' for i in range(4)):
            return False
        if not any(p['height'] == 'average' and p['cigar'] == 'dunhill' for p in people):
            return False
        if not any(p['name'] == 'Eric' and p['height'] == 'very tall' for p in people):
            return False
        if not any(people[i]['name'] == 'Arnold' and people[i + 1]['phone'] == 'huawei p50' for i in range(4)):
            return False
        if people[3]['name'] == 'Bob':
            return False
        if not any(people[i]['name'] == 'Eric' and people[i + 1]['smoothie'] == 'cherry' for i in range(4)):
            return False
        if not any(p['name'] == 'Bob' and p['cigar'] == 'dunhill' for p in people):
            return False
        if not any(p['name'] == 'Bob' and p['smoothie'] == 'dragonfruit' for p in people):
            return False
        if not any(abs(people[i]['phone'] == 'iphone 13' - people[j]['phone'] == 'oneplus 9') == 1 for i in range(5) for j in range(5) if i != j):
            return False
        if not any(p['phone'] == 'samsung galaxy s21' and p['height'] == 'short' for p in people):
            return False
        if not any(abs(people[i]['height'] == 'very tall' - people[j]['smoothie'] == 'dragonfruit') == 3 for i in range(5) for j in range(5) if i != j):
            return False
        if not any(p['name'] == 'Eric' and p['phone'] == 'iphone 13' for p in people):
            return False
        if not any(people[i]['smoothie'] == 'desert' and any(people[j]['smoothie'] == 'lime' for j in range(i + 1, 5))):
            return False
        if not any(abs(name_order.index('Arnold') - name_order.index(p for p in people if p['height'] == 'very short')[0]) == 1):
            return False

        return True

    for permutation in all_permutations:
        if is_valid_solution(permutation):
            name_order, height_order, cigar_order, smoothie_order, phone_order = permutation
            solution = [
                [str(h + 1), name_order[h], height_order[h], cigar_order[h], smoothie_order[h], phone_order[h]]
                for h in range(5)
            ]
            result = {
                "solution": {
                    "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
                    "rows": solution
                }
            }
            print(json.dumps(result))
            return

solve_puzzle()