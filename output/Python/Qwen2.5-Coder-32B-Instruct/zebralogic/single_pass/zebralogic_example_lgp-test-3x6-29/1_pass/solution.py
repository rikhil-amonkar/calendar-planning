import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3]
    names = ["Arnold", "Peter", "Eric"]
    animals = ["bird", "horse", "cat"]
    birthdays = ["jan", "sept", "april"]
    hobbies = ["photography", "cooking", "gardening"]
    drinks = ["milk", "water", "tea"]
    hair_colors = ["black", "brown", "blonde"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(animals)) * \
                       list(itertools.permutations(birthdays)) * \
                       list(itertools.permutations(hobbies)) * \
                       list(itertools.permutations(drinks)) * \
                       list(itertools.permutations(hair_colors))

    for names_perm, animals_perm, birthdays_perm, hobbies_perm, drinks_perm, hair_colors_perm in all_permutations:
        # Create a dictionary to store the solution
        solution = {
            1: {"Name": names_perm[0], "Animal": animals_perm[0], "Birthday": birthdays_perm[0], "Hobby": hobbies_perm[0], "Drink": drinks_perm[0], "HairColor": hair_colors_perm[0]},
            2: {"Name": names_perm[1], "Animal": animals_perm[1], "Birthday": birthdays_perm[1], "Hobby": hobbies_perm[1], "Drink": drinks_perm[1], "HairColor": hair_colors_perm[1]},
            3: {"Name": names_perm[2], "Animal": animals_perm[2], "Birthday": birthdays_perm[2], "Hobby": hobbies_perm[2], "Drink": drinks_perm[2], "HairColor": hair_colors_perm[2]}
        }

        # Check all constraints
        if (solution[1]["HairColor"] == "brown" and solution[1]["Hobby"] == "cooking") or \
           (solution[2]["HairColor"] == "brown" and solution[2]["Hobby"] == "cooking") or \
           (solution[3]["HairColor"] == "brown" and solution[3]["Hobby"] == "cooking"):
            if solution[3]["Birthday"] == "april":
                if solution[1]["Name"] != "Eric" and solution[2]["Name"] != "Eric":
                    if solution[2]["Animal"] == "cat":
                        if (solution[1]["HairColor"] == "blonde" and solution[2]["Drink"] != "milk") or \
                           (solution[1]["HairColor"] == "blonde" and solution[3]["Drink"] != "milk") or \
                           (solution[2]["HairColor"] == "blonde" and solution[3]["Drink"] != "milk"):
                            if solution[3]["Hobby"] == "gardening" and solution[3]["Drink"] == "milk":
                                if solution[2]["Animal"] == "cat" and solution[2]["HairColor"] == "brown":
                                    if solution[1]["Name"] == "Arnold" and solution[1]["Animal"] == "bird":
                                        if solution[3]["Drink"] == "water" and solution[3]["Hobby"] == "photography":
                                            if solution[2]["Birthday"] == "sept" and solution[3]["Name"] == "Arnold":
                                                # If all conditions are met, format the solution
                                                result = {
                                                    "solution": {
                                                        "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                                                        "rows": [
                                                            [str(house), solution[house]["Name"], solution[house]["Animal"], solution[house]["Birthday"], solution[house]["Hobby"], solution[house]["Drink"], solution[house]["HairColor"]]
                                                            for house in houses
                                                        ]
                                                    }
                                                }
                                                print(json.dumps(result))
                                                return

solve_puzzle()