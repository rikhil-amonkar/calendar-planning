#!/usr/bin/env python3
import itertools
import json

def satisfies_constraints(names, phones, heights, styles, cars):
    # Constraint 1: Peter is somewhere to the right of Eric.
    if names.index("Peter") <= names.index("Eric"):
        return False

    # Constraint 2: The person living in a colonial-style house is in the second house.
    if styles[1] != "colonial":
        return False

    # Constraint 3: The person who owns a Tesla Model 3 is the person who is very short.
    for i in range(3):
        if (cars[i] == "tesla model 3" and heights[i] != "very short") or (heights[i] == "very short" and cars[i] != "tesla model 3"):
            return False

    # Constraint 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21.
    found = False
    for i in range(2):
        if heights[i] == "short" and phones[i+1] == "samsung galaxy s21":
            found = True
    if not found:
        return False

    # Constraint 5: The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
    found = False
    for i in range(2):
        if phones[i] == "iphone 13" and phones[i+1] == "google pixel 6":
            found = True
    if not found:
        return False

    # Constraint 6: The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home.
    if styles.index("colonial") <= styles.index("ranch"):
        return False

    # Constraint 7: Arnold is in the second house.
    if names[1] != "Arnold":
        return False

    # Constraint 8: The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry.
    if cars.index("ford f150") <= cars.index("toyota camry"):
        return False

    # Constraint 9: The person who has an average height is in the first house.
    if heights[0] != "average":
        return False

    return True

def main():
    houses = [1, 2, 3]

    names_list = ["Eric", "Arnold", "Peter"]
    phones_list = ["iphone 13", "samsung galaxy s21", "google pixel 6"]
    heights_list = ["very short", "average", "short"]
    styles_list = ["colonial", "ranch", "victorian"]
    cars_list = ["tesla model 3", "toyota camry", "ford f150"]

    solution = None
    # Iterate over all possible permutations of the attributes.
    for names_perm in itertools.permutations(names_list):
        # Constraint 7: Arnold must be in the second house.
        if names_perm[1] != "Arnold":
            continue
        # Constraint 1: Peter must be to the right of Eric.
        if names_perm.index("Peter") <= names_perm.index("Eric"):
            continue

        for phones_perm in itertools.permutations(phones_list):
            # Constraint 5: Check if there is an iPhone 13 directly left of Google Pixel 6.
            valid_phone_pair = False
            for i in range(2):
                if phones_perm[i] == "iphone 13" and phones_perm[i+1] == "google pixel 6":
                    valid_phone_pair = True
                    break
            if not valid_phone_pair:
                continue

            for heights_perm in itertools.permutations(heights_list):
                # Constraint 9: The average height must be in the first house.
                if heights_perm[0] != "average":
                    continue

                for styles_perm in itertools.permutations(styles_list):
                    # Constraint 2: Colonial style must be at the second house.
                    if styles_perm[1] != "colonial":
                        continue
                    # Constraint 6: Colonial must be to the right of Ranch.
                    if styles_perm.index("colonial") <= styles_perm.index("ranch"):
                        continue

                    for cars_perm in itertools.permutations(cars_list):
                        # Constraint 8: Ford F-150 must be somewhere to the right of Toyota Camry.
                        if cars_perm.index("ford f150") <= cars_perm.index("toyota camry"):
                            continue

                        # Constraint 3: Tesla pairs with very short.
                        valid_tesla = True
                        for i in range(3):
                            if (cars_perm[i] == "tesla model 3" and heights_perm[i] != "very short") or (heights_perm[i] == "very short" and cars_perm[i] != "tesla model 3"):
                                valid_tesla = False
                                break
                        if not valid_tesla:
                            continue

                        # Constraint 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21.
                        valid_short_samsung = False
                        for i in range(2):
                            if heights_perm[i] == "short" and phones_perm[i+1] == "samsung galaxy s21":
                                valid_short_samsung = True
                                break
                        if not valid_short_samsung:
                            continue

                        # All constraints satisfied?
                        if satisfies_constraints(names_perm, phones_perm, heights_perm, styles_perm, cars_perm):
                            # Build the solution rows (houses are 1-indexed with fixed order).
                            rows = []
                            for i in range(3):
                                rows.append([
                                    str(i+1),
                                    names_perm[i],
                                    phones_perm[i],
                                    heights_perm[i],
                                    styles_perm[i],
                                    cars_perm[i]
                                ])
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
                                    "rows": rows
                                }
                            }
                            print(json.dumps(solution, indent=2))
                            return

if __name__ == "__main__":
    main()