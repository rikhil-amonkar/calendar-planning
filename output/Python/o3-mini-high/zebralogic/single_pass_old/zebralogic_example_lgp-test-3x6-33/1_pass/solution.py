#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the attributes
    names = ["Arnold", "Eric", "Peter"]
    flowers = ["carnations", "lilies", "daffodils"]
    hair_colors = ["black", "brown", "blonde"]
    sports = ["soccer", "basketball", "tennis"]
    house_styles = ["colonial", "ranch", "victorian"]
    pets = ["fish", "dog", "cat"]

    solution = None

    # There are 3 houses, indexes 0, 1, 2 correspond to houses 1, 2, 3.
    for perm_names in itertools.permutations(names):
        for perm_flowers in itertools.permutations(flowers):
            for perm_hair in itertools.permutations(hair_colors):
                for perm_sports in itertools.permutations(sports):
                    for perm_styles in itertools.permutations(house_styles):
                        for perm_pets in itertools.permutations(pets):
                            # Constraint 2: The person who has blonde hair is in the second house.
                            if perm_hair[1] != "blonde":
                                continue
                            # Constraint 3: The person who loves daffodils is the person who has blonde hair.
                            if perm_flowers[1] != "daffodils":
                                continue
                            # Constraint 7: The person who loves carnations is directly left of the person with blonde hair.
                            # Since blonde hair is in house 2, house 1 must have carnations.
                            if perm_flowers[0] != "carnations":
                                continue
                            # Constraint 8: The person who loves soccer is in the third house.
                            if perm_sports[2] != "soccer":
                                continue
                            # Constraint 10: The person living in a colonial-style house is in the third house.
                            if perm_styles[2] != "colonial":
                                continue

                            valid = True

                            # Constraint 1: The person who has a cat is the person who loves soccer.
                            for i in range(3):
                                if (perm_pets[i] == "cat" and perm_sports[i] != "soccer") or (perm_sports[i] == "soccer" and perm_pets[i] != "cat"):
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 4: Peter is the person who loves basketball.
                            # Find index of Peter, then check sport.
                            try:
                                idx_peter = perm_names.index("Peter")
                            except ValueError:
                                continue
                            if perm_sports[idx_peter] != "basketball":
                                continue

                            # Constraint 6: The person who owns a dog is the person who loves basketball.
                            for i in range(3):
                                if (perm_pets[i] == "dog" and perm_sports[i] != "basketball") or (perm_sports[i] == "basketball" and perm_pets[i] != "dog"):
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 5: Arnold is directly left of the person in a ranch-style home.
                            try:
                                idx_arnold = perm_names.index("Arnold")
                            except ValueError:
                                continue
                            # Arnold cannot be in the rightmost house if he must be directly left.
                            if idx_arnold == 2:
                                continue
                            if perm_styles[idx_arnold + 1] != "ranch":
                                continue

                            # Constraint 9: Arnold is somewhere to the left of the person who has black hair.
                            try:
                                idx_black = perm_hair.index("black")
                            except ValueError:
                                continue
                            if idx_arnold >= idx_black:
                                continue

                            # All constraints satisfied: we have a solution.
                            solution = []
                            for i in range(3):
                                # House numbers are 1-indexed.
                                house = {
                                    "House": str(i + 1),
                                    "Name": perm_names[i],
                                    "Favorite flower": perm_flowers[i],
                                    "Hair color": perm_hair[i],
                                    "Favorite sport": perm_sports[i],
                                    "House style": perm_styles[i],
                                    "Pet": perm_pets[i]
                                }
                                solution.append(house)
                            # Once a valid solution is found, break out of all loops.
                            if solution:
                                break
                        if solution:
                            break
                    if solution:
                        break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    # Prepare the result in the required JSON structure.
    header = ["House", "Name", "Favorite flower", "Hair color", "Favorite sport", "House style", "Pet"]
    rows = []
    # Ensure houses are sorted by their number (they already are in order)
    for house in solution:
        row = [house["House"], house["Name"], house["Favorite flower"], house["Hair color"],
               house["Favorite sport"], house["House style"], house["Pet"]]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()