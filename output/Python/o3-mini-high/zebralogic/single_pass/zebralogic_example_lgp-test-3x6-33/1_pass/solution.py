#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Arnold", "Eric", "Peter"]
    flowers = ["carnations", "lilies", "daffodils"]
    hair_colors = ["black", "brown", "blonde"]
    sports = ["soccer", "basketball", "tennis"]
    house_styles = ["colonial", "ranch", "victorian"]
    pets = ["fish", "dog", "cat"]

    # Iterate over all possible assignments (permutations) for each category.
    for perm_names in itertools.permutations(names):
        for perm_flowers in itertools.permutations(flowers):
            for perm_hair in itertools.permutations(hair_colors):
                # Constraint 2: The person with blonde hair is in the second house.
                if perm_hair[1] != "blonde":
                    continue
                for perm_sports in itertools.permutations(sports):
                    # Constraint 8: The person who loves soccer is in the third house.
                    if perm_sports[2] != "soccer":
                        continue
                    for perm_styles in itertools.permutations(house_styles):
                        # Constraint 10: The colonial-style house is in the third house.
                        if perm_styles[2] != "colonial":
                            continue
                        for perm_pets in itertools.permutations(pets):
                            valid = True
                            
                            # Constraint 1: The person who has a cat is the person who loves soccer.
                            for i in range(3):
                                if perm_pets[i] == "cat" and perm_sports[i] != "soccer":
                                    valid = False
                                    break
                                if perm_sports[i] == "soccer" and perm_pets[i] != "cat":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Constraint 3: The person who loves daffodils is the person who has blonde hair.
                            for i in range(3):
                                if perm_flowers[i] == "daffodils" and perm_hair[i] != "blonde":
                                    valid = False
                                    break
                                if perm_hair[i] == "blonde" and perm_flowers[i] != "daffodils":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Constraint 4: Peter is the person who loves basketball.
                            idx_peter = perm_names.index("Peter")
                            if perm_sports[idx_peter] != "basketball":
                                continue
                            
                            # Constraint 5: Arnold is directly left of the person in a ranch-style home.
                            idx_arnold = perm_names.index("Arnold")
                            if idx_arnold == 2 or perm_styles[idx_arnold + 1] != "ranch":
                                continue
                            
                            # Constraint 6: The person who owns a dog is the person who loves basketball.
                            for i in range(3):
                                if perm_pets[i] == "dog" and perm_sports[i] != "basketball":
                                    valid = False
                                    break
                                if perm_sports[i] == "basketball" and perm_pets[i] != "dog":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Constraint 7: The person who loves carnations is directly left of the person who has blonde hair.
                            idx_carnations = perm_flowers.index("carnations")
                            if idx_carnations == 2 or perm_hair[idx_carnations + 1] != "blonde":
                                continue
                            
                            # Constraint 9: Arnold is somewhere to the left of the person who has black hair.
                            idx_black = perm_hair.index("black")
                            if idx_arnold >= idx_black:
                                continue
                            
                            # If all constraints are satisfied, build the solution.
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                                    "rows": [
                                        ["1", perm_names[0], perm_flowers[0], perm_hair[0], perm_sports[0], perm_styles[0], perm_pets[0]],
                                        ["2", perm_names[1], perm_flowers[1], perm_hair[1], perm_sports[1], perm_styles[1], perm_pets[1]],
                                        ["3", perm_names[2], perm_flowers[2], perm_hair[2], perm_sports[2], perm_styles[2], perm_pets[2]]
                                    ]
                                }
                            }
                            print(json.dumps(solution))
                            return

if __name__ == '__main__':
    main()