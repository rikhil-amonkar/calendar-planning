import itertools
import json

def solve_puzzle():
    names = ['Eric', 'Peter', 'Arnold']
    smoothies = ['cherry', 'watermelon', 'desert']
    flowers = ['carnations', 'lilies', 'daffodils']
    animals = ['cat', 'horse', 'bird']
    hobbies = ['photography', 'cooking', 'gardening']

    for name_p in itertools.permutations(names):
        for smoothie_p in itertools.permutations(smoothies):
            for flower_p in itertools.permutations(flowers):
                for animal_p in itertools.permutations(animals):
                    for hobby_p in itertools.permutations(hobbies):
                        # Clue 8: Photography enthusiast is Eric
                        try:
                            photo_idx = hobby_p.index('photography')
                            if name_p[photo_idx] != 'Eric':
                                continue
                        except ValueError:
                            continue

                        # Clue 3: Cooking hobbyist likes Desert smoothie
                        try:
                            cooking_idx = hobby_p.index('cooking')
                            if smoothie_p[cooking_idx] != 'desert':
                                continue
                        except ValueError:
                            continue

                        # Clue 6: Daffodils lover is Desert smoothie lover
                        try:
                            daffodils_idx = flower_p.index('daffodils')
                            if smoothie_p[daffodils_idx] != 'desert':
                                continue
                        except ValueError:
                            continue

                        # Clue 4: Gardening hobbyist loves carnations
                        try:
                            gardening_idx = hobby_p.index('gardening')
                            if flower_p[gardening_idx] != 'carnations':
                                continue
                        except ValueError:
                            continue

                        # Clue 2: Bird keeper likes Cherry smoothies
                        try:
                            bird_idx = animal_p.index('bird')
                            if smoothie_p[bird_idx] != 'cherry':
                                continue
                        except ValueError:
                            continue

                        # Clue 7: Watermelon smoothie lover keeps horses
                        try:
                            watermelon_idx = smoothie_p.index('watermelon')
                            if animal_p[watermelon_idx] != 'horse':
                                continue
                        except ValueError:
                            continue

                        # Clue 5: Cooking is directly left of Peter
                        if cooking_idx + 1 >= 3 or name_p[cooking_idx + 1] != 'Peter':
                            continue

                        # Clue 1: Horse and photography are adjacent
                        try:
                            horse_idx = animal_p.index('horse')
                            photo_idx = hobby_p.index('photography')
                            if abs(horse_idx - photo_idx) != 1:
                                continue
                        except ValueError:
                            continue

                        # Build solution
                        rows = []
                        for i in range(3):
                            house_num = str(i + 1)
                            rows.append([
                                house_num,
                                name_p[i],
                                smoothie_p[i],
                                flower_p[i],
                                animal_p[i],
                                hobby_p[i]
                            ])

                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                                "rows": rows
                            }
                        }

                        print(json.dumps(solution))
                        return

solve_puzzle()