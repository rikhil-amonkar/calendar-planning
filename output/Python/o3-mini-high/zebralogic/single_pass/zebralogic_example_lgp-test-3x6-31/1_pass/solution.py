#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    names = ["Eric", "Peter", "Arnold"]
    drinks = ["milk", "water", "tea"]
    vacations = ["mountain", "city", "beach"]
    housestyles = ["colonial", "victorian", "ranch"]
    animals = ["cat", "bird", "horse"]
    birthdays = ["jan", "sept", "april"]

    solution = None
    # Iterate over all possible assignments (permutations) for each category.
    for perm_names in itertools.permutations(names):
        for perm_drinks in itertools.permutations(drinks):
            # Constraint 9: Eric drinks water.
            if perm_drinks[perm_names.index("Eric")] != "water":
                continue
            for perm_vacations in itertools.permutations(vacations):
                # Constraint 4: The person who drinks water must enjoy mountain retreats.
                if perm_drinks.index("water") != perm_vacations.index("mountain"):
                    continue
                # Constraint 7: Peter prefers city breaks.
                if perm_vacations[perm_names.index("Peter")] != "city":
                    continue
                for perm_housestyles in itertools.permutations(housestyles):
                    # Constraint 1: The colonial house is to the left of the milk drinker.
                    if perm_housestyles.index("colonial") >= perm_drinks.index("milk"):
                        continue
                    # Constraint 2: The person who prefers city breaks is directly left of the Victorian house.
                    pos_city = perm_vacations.index("city")
                    if pos_city == 2 or perm_housestyles[pos_city + 1] != "victorian":
                        continue
                    # Constraint 6: The Victorian house must be somewhere to the right of the beach lover.
                    if perm_vacations.index("beach") >= perm_housestyles.index("victorian"):
                        continue
                    for perm_animals in itertools.permutations(animals):
                        # Constraint 5: Peter keeps the horses.
                        if perm_animals[perm_names.index("Peter")] != "horse":
                            continue
                        for perm_birthdays in itertools.permutations(birthdays):
                            # Constraint 8: The person who enjoys mountain retreats has a birthday in April.
                            if perm_vacations.index("mountain") != perm_birthdays.index("april"):
                                continue
                            # Constraint 3: The person whose birthday is in January is directly left of the cat lover.
                            pos_jan = perm_birthdays.index("jan")
                            if pos_jan == 2 or perm_animals[pos_jan + 1] != "cat":
                                continue
                            # All constraints satisfied; construct the solution.
                            houses = [str(i+1) for i in range(3)]
                            solution = list(zip(houses, perm_names, perm_drinks, perm_vacations, perm_housestyles, perm_animals, perm_birthdays))
                            # Exit all loops.
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

    return solution

def main():
    sol = solve_puzzle()
    # Prepare the JSON output in the exact required structure.
    output = {
        "solution": {
            "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
            "rows": [list(row) for row in sol] if sol is not None else []
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()