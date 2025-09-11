import itertools
import json

# Define the categories
names = ['Arnold', 'Eric', 'Peter']
flowers = ['carnations', 'lilies', 'daffodils']
hair_colors = ['black', 'brown', 'blonde']
sports = ['soccer', 'basketball', 'tennis']
house_styles = ['colonial', 'ranch', 'victorian']
pets = ['fish', 'dog', 'cat']

found = False

for name_perm in itertools.permutations(names):
    for flower_perm in itertools.permutations(flowers):
        # Check clue 7: carnations in house 1 (index 0)
        if flower_perm[0] != 'carnations':
            continue
        # Check clue 3: daffodils in house 2 (index 1)
        if flower_perm[1] != 'daffodils':
            continue
        for hair_color_perm in itertools.permutations(hair_colors):
            # Check clue 2: house 2 has blonde
            if hair_color_perm[1] != 'blonde':
                continue
            for sport_perm in itertools.permutations(sports):
                # Check clue 8: soccer in house 3 (index 2)
                if sport_perm[2] != 'soccer':
                    continue
                # Check clue 4: Peter's sport is basketball
                peter_index = name_perm.index('Peter')
                if sport_perm[peter_index] != 'basketball':
                    continue
                for house_style_perm in itertools.permutations(house_styles):
                    # Check clue 10: house 3 is colonial
                    if house_style_perm[2] != 'colonial':
                        continue
                    # Check clue 5: Arnold directly left of ranch
                    arnold_index = name_perm.index('Arnold')
                    if arnold_index + 1 >= 3 or house_style_perm[arnold_index + 1] != 'ranch':
                        continue
                    for pet_perm in itertools.permutations(pets):
                        # Check clue 1: cat and soccer are same person (house 3)
                        soccer_index = 2  # from clue 8
                        if pet_perm[soccer_index] != 'cat':
                            continue
                        # Check clue 6: dog owner loves basketball (Peter's pet is dog)
                        if pet_perm[peter_index] != 'dog':
                            continue
                        # Check clue 9: Arnold is left of black hair
                        black_hair_index = -1
                        for i in range(3):
                            if hair_color_perm[i] == 'black':
                                black_hair_index = i
                                break
                        if arnold_index >= black_hair_index:
                            continue
                        # All constraints satisfied. Build the solution
                        solution_rows = []
                        for i in range(3):
                            solution_rows.append([
                                str(i+1),
                                name_perm[i],
                                flower_perm[i],
                                hair_color_perm[i],
                                sport_perm[i],
                                house_style_perm[i],
                                pet_perm[i]
                            ])
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                                "rows": solution_rows
                            }
                        }
                        print(json.dumps(solution))
                        found = True
                        # Exit all loops
                        break
                    if found:
                        break
                if found:
                    break
            if found:
                break
    if found:
        break