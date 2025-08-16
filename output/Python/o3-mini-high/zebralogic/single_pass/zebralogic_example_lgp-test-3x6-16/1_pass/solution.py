#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Eric", "Peter", "Arnold"]
    drinks = ["tea", "water", "milk"]
    nationalities = ["dane", "brit", "swede"]
    educations = ["high school", "associate", "bachelor"]
    housestyles = ["victorian", "colonial", "ranch"]
    smoothies = ["cherry", "watermelon", "desert"]

    found_solution = None

    for names_perm in itertools.permutations(names):
        for drinks_perm in itertools.permutations(drinks):
            for nat_perm in itertools.permutations(nationalities):
                for edu_perm in itertools.permutations(educations):
                    # Constraint 3: The person with a bachelor's degree is in the second house.
                    if edu_perm[1] != "bachelor":
                        continue
                    for house_perm in itertools.permutations(housestyles):
                        # Constraint 6: The person residing in a Victorian house is not in the first house.
                        if house_perm[0] == "victorian":
                            continue
                        for smooth_perm in itertools.permutations(smoothies):
                            valid = True
                            # Check constraints that apply house by house.
                            for i in range(3):
                                # Constraint 2: The person who likes milk is the person in a ranch-style home.
                                # Constraint 9: The person in a ranch-style home is the person with the high school diploma.
                                if drinks_perm[i] == "milk":
                                    if house_perm[i] != "ranch":
                                        valid = False
                                        break
                                if house_perm[i] == "ranch":
                                    if drinks_perm[i] != "milk" or edu_perm[i] != "high school":
                                        valid = False
                                        break
                                # Constraint 4: The person with a high school diploma is the Dane.
                                if edu_perm[i] == "high school":
                                    if nat_perm[i] != "dane":
                                        valid = False
                                        break
                                # Constraint 7: The person who likes Cherry smoothies is the person living in a colonial-style house.
                                # (Assuming bidirectional relation)
                                if smooth_perm[i] == "cherry":
                                    if house_perm[i] != "colonial":
                                        valid = False
                                        break
                                if house_perm[i] == "colonial":
                                    if smooth_perm[i] != "cherry":
                                        valid = False
                                        break
                                # Constraint 5: The Desert smoothie lover is the Swedish person.
                                if smooth_perm[i] == "desert":
                                    if nat_perm[i] != "swede":
                                        valid = False
                                        break
                                if nat_perm[i] == "swede":
                                    if smooth_perm[i] != "desert":
                                        valid = False
                                        break
                            if not valid:
                                continue
                            # Constraint 1: There is one house between Eric and the tea drinker.
                            try:
                                eric_index = names_perm.index("Eric")
                                tea_index = drinks_perm.index("tea")
                            except ValueError:
                                continue
                            if abs(eric_index - tea_index) != 2:
                                continue
                            # Constraint 8: Arnold is somewhere to the right of the person residing in a Victorian house.
                            try:
                                victorian_index = house_perm.index("victorian")
                                arnold_index = names_perm.index("Arnold")
                            except ValueError:
                                continue
                            if arnold_index <= victorian_index:
                                continue

                            # All constraints satisfied.
                            found_solution = (names_perm, drinks_perm, nat_perm, edu_perm, house_perm, smooth_perm)
                            break
                        if found_solution:
                            break
                    if found_solution:
                        break
                if found_solution:
                    break
            if found_solution:
                break
        if found_solution:
            break

    if found_solution:
        names_sol, drinks_sol, nat_sol, edu_sol, house_sol, smooth_sol = found_solution
        solution = {
            "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
            "rows": [
                ["1", names_sol[0], drinks_sol[0], nat_sol[0], edu_sol[0], house_sol[0], smooth_sol[0]],
                ["2", names_sol[1], drinks_sol[1], nat_sol[1], edu_sol[1], house_sol[1], smooth_sol[1]],
                ["3", names_sol[2], drinks_sol[2], nat_sol[2], edu_sol[2], house_sol[2], smooth_sol[2]]
            ]
        }
        result = {"solution": solution}
    else:
        result = {"solution": {"header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"], "rows": []}}

    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()