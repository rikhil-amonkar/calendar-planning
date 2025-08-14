#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Arnold", "Peter", "Eric"]
    animals = ["bird", "horse", "cat"]
    birthdays = ["jan", "sept", "april"]
    hobbies = ["photography", "cooking", "gardening"]
    drinks = ["milk", "water", "tea"]
    hairs = ["black", "brown", "blonde"]

    solution = None

    # Iterate over all possible assignments
    for perm_names in itertools.permutations(names):
        # Constraint 3: Eric is not in the first house.
        if perm_names[0] == "Eric":
            continue
        for perm_animals in itertools.permutations(animals):
            # Constraint 4: The cat lover is in the second house.
            if perm_animals[1] != "cat":
                continue
            for perm_birthdays in itertools.permutations(birthdays):
                # Constraint 2: The person whose birthday is in April is in the third house.
                if perm_birthdays[2] != "april":
                    continue
                for perm_hobbies in itertools.permutations(hobbies):
                    for perm_drinks in itertools.permutations(drinks):
                        for perm_hairs in itertools.permutations(hairs):
                            houses = []
                            for i in range(3):
                                house = {
                                    "House": str(i+1),
                                    "Name": perm_names[i],
                                    "animal": perm_animals[i],
                                    "birthday": perm_birthdays[i],
                                    "hobby": perm_hobbies[i],
                                    "drink": perm_drinks[i],
                                    "hair": perm_hairs[i]
                                }
                                houses.append(house)

                            valid = True

                            # Constraint 1: The person who has brown hair is the person who loves cooking.
                            for house in houses:
                                if house["hair"] == "brown" and house["hobby"] != "cooking":
                                    valid = False
                                    break
                                if house["hobby"] == "cooking" and house["hair"] != "brown":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 5: The person who has blonde hair is somewhere to the left of the person who likes milk.
                            idx_blonde = None
                            idx_milk = None
                            for i, house in enumerate(houses):
                                if house["hair"] == "blonde":
                                    idx_blonde = i
                                if house["drink"] == "milk":
                                    idx_milk = i
                            if idx_blonde is None or idx_milk is None or idx_blonde >= idx_milk:
                                continue

                            # Constraint 6: The person who enjoys gardening is the person who likes milk.
                            for house in houses:
                                if house["hobby"] == "gardening" and house["drink"] != "milk":
                                    valid = False
                                    break
                                if house["drink"] == "milk" and house["hobby"] != "gardening":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 7: The cat lover is the person who has brown hair.
                            # Since the cat lover is in the second house, ensure its hair is brown.
                            if houses[1]["hair"] != "brown":
                                continue

                            # Constraint 8: Arnold is the bird keeper.
                            for house in houses:
                                if house["Name"] == "Arnold" and house["animal"] != "bird":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 9: The one who only drinks water is the photography enthusiast.
                            for house in houses:
                                if house["drink"] == "water" and house["hobby"] != "photography":
                                    valid = False
                                    break
                                if house["hobby"] == "photography" and house["drink"] != "water":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 10: The person whose birthday is in September is directly left of Arnold.
                            idx_sept = None
                            idx_arnold = None
                            for i, house in enumerate(houses):
                                if house["birthday"] == "sept":
                                    idx_sept = i
                                if house["Name"] == "Arnold":
                                    idx_arnold = i
                            if idx_sept is None or idx_arnold is None or idx_sept + 1 != idx_arnold:
                                continue

                            # All constraints satisfied; this is the solution.
                            solution = houses
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

    # Prepare output in the required JSON format.
    header = ["House", "Name", "animal", "birthday", "hobby", "drink", "hair"]
    rows = []
    if solution:
        # Ensure houses are in order House 1, House 2, House 3.
        for house in solution:
            row = [
                house["House"],
                house["Name"],
                house["animal"],
                house["birthday"],
                house["hobby"],
                house["drink"],
                house["hair"]
            ]
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