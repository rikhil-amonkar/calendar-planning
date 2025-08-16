#!/usr/bin/env python3
import itertools
import json

def main():
    # Define possible attributes.
    names = ["Arnold", "Peter", "Eric"]
    animals = ["bird", "horse", "cat"]
    birthdays = ["jan", "sept", "april"]
    hobbies = ["photography", "cooking", "gardening"]
    drinks = ["milk", "water", "tea"]
    hair_colors = ["black", "brown", "blonde"]

    solution = None

    # Generate all possible assignments using permutations.
    for names_perm in itertools.permutations(names):
        # Clue 3: Eric is not in the first house.
        if names_perm[0] == "Eric":
            continue
        for animals_perm in itertools.permutations(animals):
            # Clue 4: The cat lover is in the second house.
            if animals_perm[1] != "cat":
                continue
            for birthdays_perm in itertools.permutations(birthdays):
                # Clue 2: The person whose birthday is in April is in the third house.
                if birthdays_perm[2] != "april":
                    continue
                for hobbies_perm in itertools.permutations(hobbies):
                    for drinks_perm in itertools.permutations(drinks):
                        for hair_perm in itertools.permutations(hair_colors):
                            # Build the list of houses (houses numbered 1 to 3 from left to right).
                            houses = []
                            for i in range(3):
                                house = {
                                    "House": str(i+1),
                                    "Name": names_perm[i],
                                    "Animal": animals_perm[i],
                                    "Birthday": birthdays_perm[i],
                                    "Hobby": hobbies_perm[i],
                                    "Drink": drinks_perm[i],
                                    "HairColor": hair_perm[i]
                                }
                                houses.append(house)

                            valid = True
                            
                            # Constraint 1: The person who has brown hair is the person who loves cooking.
                            for house in houses:
                                if house["HairColor"] == "brown" and house["Hobby"] != "cooking":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 5: The person who has blonde hair is somewhere to the left of the person who likes milk.
                            blonde_index = None
                            milk_index = None
                            for i, house in enumerate(houses):
                                if house["HairColor"] == "blonde":
                                    blonde_index = i
                                if house["Drink"] == "milk":
                                    milk_index = i
                            if blonde_index is None or milk_index is None or blonde_index >= milk_index:
                                continue

                            # Constraint 6: The person who enjoys gardening is the person who likes milk.
                            # This implies a one-to-one relationship.
                            for house in houses:
                                if house["Hobby"] == "gardening" and house["Drink"] != "milk":
                                    valid = False
                                    break
                                if house["Drink"] == "milk" and house["Hobby"] != "gardening":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 7: The cat lover is the person who has brown hair.
                            # Since the cat lover is in the second house, check that.
                            if houses[1]["HairColor"] != "brown":
                                continue

                            # Constraint 8: Arnold is the bird keeper.
                            for house in houses:
                                if house["Name"] == "Arnold" and house["Animal"] != "bird":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 9: The one who only drinks water is the photography enthusiast.
                            for house in houses:
                                if house["Drink"] == "water" and house["Hobby"] != "photography":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 10: The person whose birthday is in September is directly left of Arnold.
                            arnold_index = None
                            for i, house in enumerate(houses):
                                if house["Name"] == "Arnold":
                                    arnold_index = i
                                    break
                            # Arnold cannot be in the first house.
                            if arnold_index is None or arnold_index == 0:
                                continue
                            if houses[arnold_index - 1]["Birthday"] != "sept":
                                continue

                            # If all constraints are satisfied, we have found the solution.
                            solution = houses
                            break
                        if solution is not None:
                            break
                    if solution is not None:
                        break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    # Prepare output in the specified JSON structure.
    output = {
        "solution": {
            "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
            "rows": []
        }
    }

    if solution:
        # Ensure houses are in order by their house number.
        solution_sorted = sorted(solution, key=lambda x: int(x["House"]))
        for house in solution_sorted:
            row = [
                house["House"],
                house["Name"],
                house["Animal"],
                house["Birthday"],
                house["Hobby"],
                house["Drink"],
                house["HairColor"]
            ]
            output["solution"]["rows"].append(row)

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()