import itertools
import json

names_options = ['Peter', 'Arnold', 'Alice', 'Eric']
flowers_options = ['roses', 'daffodils', 'carnations', 'lilies']
hobbies_options = ['photography', 'painting', 'cooking', 'gardening']
pets_options = ['dog', 'fish', 'bird', 'cat']
colors_options = ['red', 'yellow', 'green', 'white']
housestyles_options = ['craftsman', 'colonial', 'ranch', 'victorian']

valid_names = [p for p in itertools.permutations(names_options) if p[1] == 'Arnold']
valid_housestyles = [p for p in itertools.permutations(housestyles_options) if p[1] == 'craftsman']

for names_p in valid_names:
    eric_idx = names_p.index('Eric')
    for housestyles_p in valid_housestyles:
        victorian_pos = housestyles_p.index('victorian')
        if names_p[victorian_pos] != 'Eric':
            continue
        for flowers_p in itertools.permutations(flowers_options):
            if flowers_p[3] == 'daffodils':
                continue
            for hobbies_p in itertools.permutations(hobbies_options):
                for pets_p in itertools.permutations(pets_options):
                    valid_pets = True
                    for i in range(4):
                        if hobbies_p[i] == 'photography' and pets_p[i] != 'dog':
                            valid_pets = False
                            break
                    if not valid_pets:
                        continue
                    if pets_p[eric_idx] != 'cat':
                        continue
                    for colors_p in itertools.permutations(colors_options):
                        clue13_ok = True
                        for i in range(4):
                            if housestyles_p[i] == 'colonial' and colors_p[i] != 'red':
                                clue13_ok = False
                                break
                        if not clue13_ok:
                            continue
                        clue5_ok = True
                        for i in range(4):
                            if flowers_p[i] == 'roses' and colors_p[i] != 'red':
                                clue5_ok = False
                                break
                        if not clue5_ok:
                            continue
                        clue12_ok = True
                        for i in range(4):
                            if flowers_p[i] == 'daffodils' and colors_p[i] != 'yellow':
                                clue12_ok = False
                                break
                        if not clue12_ok:
                            continue
                        clue8_ok = True
                        for i in range(4):
                            if pets_p[i] == 'fish' and colors_p[i] != 'white':
                                clue8_ok = False
                                break
                        if not clue8_ok:
                            continue
                        clue10_ok = True
                        for i in range(4):
                            if colors_p[i] == 'white' and flowers_p[i] != 'carnations':
                                clue10_ok = False
                                break
                        if not clue10_ok:
                            continue
                        red_indices = [i for i, c in enumerate(colors_p) if c == 'red']
                        red_idx = red_indices[0]
                        cook_idx = hobbies_p.index('cooking')
                        if cook_idx <= red_idx:
                            continue
                        white_idx = colors_p.index('white')
                        try:
                            gardening_idx = hobbies_p.index('gardening')
                        except ValueError:
                            continue
                        if white_idx <= gardening_idx:
                            continue
                        roses_idx = flowers_p.index('roses')
                        peter_idx = names_p.index('Peter')
                        if roses_idx <= peter_idx:
                            continue
                        solution_rows = []
                        for i in range(4):
                            house_num = str(i + 1)
                            solution_rows.append([
                                house_num,
                                names_p[i],
                                flowers_p[i],
                                hobbies_p[i],
                                pets_p[i],
                                colors_p[i],
                                housestyles_p[i]
                            ])
                        output = {
                            "solution": {
                                "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
                                "rows": solution_rows
                            }
                        }
                        print(json.dumps(output))
                        exit()