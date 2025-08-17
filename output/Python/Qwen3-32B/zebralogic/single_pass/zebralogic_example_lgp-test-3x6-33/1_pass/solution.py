import itertools
import json

# Categories
names_list = ['Arnold', 'Eric', 'Peter']
flowers_list = ['carnations', 'lilies', 'daffodils']
haircolors_list = ['black', 'brown', 'blonde']
sports_list = ['soccer', 'basketball', 'tennis']
styles_list = ['colonial', 'ranch', 'victorian']
pets_list = ['fish', 'dog', 'cat']

solution_found = None

for names in itertools.permutations(names_list):
    for flowers in itertools.permutations(flowers_list):
        for haircolors in itertools.permutations(haircolors_list):
            # Check clue 2: Blonde hair in house 2
            if haircolors[1] != 'blonde':
                continue
            # Check clue 3: Daffodils lover has blonde hair
            daffodils_idx = flowers.index('daffodils')
            if haircolors[daffodils_idx] != 'blonde':
                continue
            for sports in itertools.permutations(sports_list):
                # Check clue 4: Peter loves basketball
                peter_idx = names.index('Peter')
                if sports[peter_idx] != 'basketball':
                    continue
                # Check clue 8: Soccer in house 3
                if sports[2] != 'soccer':
                    continue
                for styles in itertools.permutations(styles_list):
                    # Check clue 10: Colonial in house 3
                    if styles[2] != 'colonial':
                        continue
                    # Check clue 5: Arnold directly left of ranch
                    arnold_idx = names.index('Arnold')
                    if (arnold_idx + 1 >= 3) or (styles[arnold_idx + 1] != 'ranch'):
                        continue
                    for pets in itertools.permutations(pets_list):
                        # Check clue 6: Dog owner plays basketball
                        dog_idx = pets.index('dog')
                        if sports[dog_idx] != 'basketball':
                            continue
                        # Check clue 1 and 8: Soccer lover has cat in house 3
                        if pets[2] != 'cat':
                            continue
                        # Check clue 7: Carnations directly left of blonde (house 2)
                        if flowers[0] != 'carnations':
                            continue
                        # Check clue 9: Arnold is left of black hair
                        black_hair_idx = haircolors.index('black')
                        if arnold_idx >= black_hair_idx:
                            continue
                        # All constraints satisfied
                        rows = []
                        for i in range(3):
                            house_num = str(i + 1)
                            row = [
                                house_num,
                                names[i],
                                flowers[i],
                                haircolors[i],
                                sports[i],
                                styles[i],
                                pets[i]
                            ]
                            rows.append(row)
                        solution_found = {
                            "solution": {
                                "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                                "rows": rows
                            }
                        }
                        break
                    if solution_found:
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break

print(json.dumps(solution_found, indent=2))