import itertools
import json
import sys

def solve_puzzle():
    names_list = ["Arnold", "Peter", "Eric"]
    animals_list = ["bird", "horse", "cat"]
    birthdays_list = ["jan", "sept", "april"]
    hobbies_list = ["photography", "cooking", "gardening"]
    drinks_list = ["milk", "water", "tea"]
    haircolors_list = ["black", "brown", "blonde"]

    for names in itertools.permutations(names_list):
        # Constraint 3: Eric is not in the first house.
        if names[0] == "Eric":
            continue
        for animals in itertools.permutations(animals_list):
            # Constraint 4: The cat lover is in the second house.
            if animals[1] != "cat":
                continue
            for birthdays in itertools.permutations(birthdays_list):
                # Constraint 2: The person whose birthday is in April is in the third house.
                if birthdays[2] != "april":
                    continue
                for hobbies in itertools.permutations(hobbies_list):
                    # Constraint 1: The person with brown hair is the person who loves cooking.
                    valid = True
                    for i in range(3):
                        if hobbies[i] == "cooking":
                            # Later we will check hair color; here we need consistency
                            pass
                    for drinks in itertools.permutations(drinks_list):
                        for haircolors in itertools.permutations(haircolors_list):
                            valid = True
                            # Constraint 1 & its converse:
                            for i in range(3):
                                if haircolors[i] == "brown" and hobbies[i] != "cooking":
                                    valid = False
                                    break
                                if hobbies[i] == "cooking" and haircolors[i] != "brown":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 5: The person with blonde hair is somewhere to the left of the person who likes milk.
                            try:
                                index_blonde = haircolors.index("blonde")
                                index_milk = drinks.index("milk")
                            except ValueError:
                                continue
                            if index_blonde >= index_milk:
                                continue

                            # Constraint 6: The person who enjoys gardening is the person who likes milk.
                            for i in range(3):
                                if hobbies[i] == "gardening" and drinks[i] != "milk":
                                    valid = False
                                    break
                                if drinks[i] == "milk" and hobbies[i] != "gardening":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 7: The cat lover is the person who has brown hair.
                            for i in range(3):
                                if animals[i] == "cat" and haircolors[i] != "brown":
                                    valid = False
                                    break
                                if haircolors[i] == "brown" and animals[i] != "cat":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 8: Arnold is the bird keeper.
                            try:
                                index_arnold = names.index("Arnold")
                            except ValueError:
                                continue
                            if animals[index_arnold] != "bird":
                                continue

                            # Constraint 9: The one who only drinks water is the photography enthusiast.
                            for i in range(3):
                                if drinks[i] == "water" and hobbies[i] != "photography":
                                    valid = False
                                    break
                                if hobbies[i] == "photography" and drinks[i] != "water":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 10: The person whose birthday is in September is directly left of Arnold.
                            if index_arnold == 0:
                                continue
                            if birthdays[index_arnold - 1] != "sept":
                                continue

                            # If all constraints are met, construct the solution.
                            solution_rows = []
                            for i in range(3):
                                solution_rows.append([
                                    str(i + 1),
                                    names[i],
                                    animals[i],
                                    birthdays[i],
                                    hobbies[i],
                                    drinks[i],
                                    haircolors[i]
                                ])
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                                    "rows": solution_rows
                                }
                            }
                            print(json.dumps(result, indent=2))
                            sys.exit(0)

if __name__ == '__main__':
    solve_puzzle()