import json
from itertools import permutations, product

def solve_puzzle():
    categories = [
        ['Eric', 'Arnold', 'Peter'],  # Name
        ['mountain', 'city', 'beach'],  # Vacation
        ['very short', 'average', 'short'],  # Height
        ['carnations', 'daffodils', 'lilies'],  # Flower
        ['brown', 'black', 'blonde'],  # HairColor
        ['associate', 'bachelor', 'high school']  # Education
    ]

    all_perms = [list(permutations(cat)) for cat in categories]

    def is_valid(combo):
        names, vacations, heights, flowers, hairs, educations = combo

        # Clue 1: Peter's height is average
        peter_idx = names.index('Peter')
        if heights[peter_idx] != 'average':
            return False

        # Clue 2: Arnold has daffodils
        arnold_idx = names.index('Arnold')
        if flowers[arnold_idx] != 'daffodils':
            return False

        # Clue 3: very short not in house 2 (index 1)
        if heights.index('very short') == 1:
            return False

        # Clue 4: first house (index 0) has beach vacation
        if vacations[0] != 'beach':
            return False

        # Clue 5: third house (index 2) has high school
        if educations[2] != 'high school':
            return False

        # Clue 6: short is to the right of very short
        vs_idx = heights.index('very short')
        s_idx = heights.index('short')
        if vs_idx >= s_idx:
            return False

        # Clue 7: lilies is Eric's flower
        lilies_idx = flowers.index('lilies')
        if names[lilies_idx] != 'Eric':
            return False

        # Clue 8: lilies person has bachelor
        if educations[lilies_idx] != 'bachelor':
            return False

        # Clue 9: city is to the right of Peter
        city_idx = vacations.index('city')
        if city_idx <= peter_idx:
            return False

        # Clue 10: third house has blonde
        if hairs[2] != 'blonde':
            return False

        # Clue 11: beach (index 0) has brown hair
        if hairs[0] != 'brown':
            return False

        return True

    for combination in product(*all_perms):
        if is_valid(combination):
            names, vacations, heights, flowers, hairs, educations = combination
            rows = []
            for i in range(3):
                house = str(i + 1)
                row = [
                    house,
                    names[i],
                    vacations[i],
                    heights[i],
                    flowers[i],
                    hairs[i],
                    educations[i]
                ]
                rows.append(row)
            solution = {
                "solution": {
                    "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
                    "rows": rows
                }
            }
            print(json.dumps(solution, indent=2))
            return

solve_puzzle()