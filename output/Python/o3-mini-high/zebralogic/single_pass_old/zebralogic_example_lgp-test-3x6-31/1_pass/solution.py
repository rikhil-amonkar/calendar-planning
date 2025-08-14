#!/usr/bin/env python3
import itertools
import json

def satisfies_constraints(houses):
    # houses is a list of dictionaries representing houses in order (House 1 is index 0, House 2 index 1, House 3 index 2)

    # Clue 1:
    # "The person living in a colonial-style house is somewhere to the left of the person who likes milk."
    # There must be at least one house with "colonial" that is at a lower index than at least one house with drink "milk".
    colonial_found = False
    valid1 = False
    for i, house in enumerate(houses):
        if house["House Style"] == "colonial":
            colonial_found = True
            # Check if any house to the right has drink "milk"
            if any(h["Drink"] == "milk" for h in houses[i+1:]):
                valid1 = True
            else:
                return False
    if not colonial_found or not valid1:
        return False

    # Clue 2:
    # "The person who prefers city breaks is directly left of the person residing in a Victorian house."
    valid2 = False
    for i in range(len(houses) - 1):
        if houses[i]["Vacation"] == "city" and houses[i+1]["House Style"] == "victorian":
            valid2 = True
    if not valid2:
        return False

    # Clue 3:
    # "The person whose birthday is in January is directly left of the cat lover."
    valid3 = False
    for i in range(len(houses) - 1):
        if houses[i]["Birthday"] == "jan" and houses[i+1]["Animal"] == "cat":
            valid3 = True
    if not valid3:
        return False

    # Clue 4:
    # "The one who only drinks water is the person who enjoys mountain retreats."
    for house in houses:
        if house["Drink"] == "water" and house["Vacation"] != "mountain":
            return False
        if house["Vacation"] == "mountain" and house["Drink"] != "water":
            return False

    # Clue 5:
    # "The person who keeps horses is Peter."
    for house in houses:
        if house["Animal"] == "horse" and house["Name"] != "Peter":
            return False
        if house["Name"] == "Peter" and house["Animal"] != "horse":
            return False

    # Clue 6:
    # "The person residing in a Victorian house is somewhere to the right of the person who loves beach vacations."
    valid6 = False
    for i, house in enumerate(houses):
        if house["House Style"] == "victorian":
            if any(left["Vacation"] == "beach" for left in houses[:i]):
                valid6 = True
            else:
                return False
    if not valid6:
        return False

    # Clue 7:
    # "Peter is the person who prefers city breaks."
    for house in houses:
        if house["Name"] == "Peter" and house["Vacation"] != "city":
            return False

    # Clue 8:
    # "The person who enjoys mountain retreats is the person whose birthday is in April."
    for house in houses:
        if house["Vacation"] == "mountain" and house["Birthday"] != "april":
            return False
        if house["Birthday"] == "april" and house["Vacation"] != "mountain":
            return False

    # Clue 9:
    # "Eric is the one who only drinks water."
    for house in houses:
        if house["Name"] == "Eric" and house["Drink"] != "water":
            return False

    return True

def main():
    houses_numbers = [1, 2, 3]
    # Attributes as given in the puzzle.
    names = ["Eric", "Peter", "Arnold"]
    drinks = ["milk", "water", "tea"]
    vacations = ["mountain", "city", "beach"]
    house_styles = ["colonial", "victorian", "ranch"]
    animals = ["cat", "bird", "horse"]
    birthdays = ["jan", "sept", "april"]

    solution = None

    # Try all permutations of attributes for the 3 houses.
    for perm_names in itertools.permutations(names):
        for perm_drinks in itertools.permutations(drinks):
            for perm_vacations in itertools.permutations(vacations):
                for perm_house_styles in itertools.permutations(house_styles):
                    for perm_animals in itertools.permutations(animals):
                        for perm_birthdays in itertools.permutations(birthdays):
                            # Build assignment for houses 1, 2, 3:
                            houses = []
                            for i in range(3):
                                house = {
                                    "House": str(houses_numbers[i]),
                                    "Name": perm_names[i],
                                    "Drink": perm_drinks[i],
                                    "Vacation": perm_vacations[i],
                                    "House Style": perm_house_styles[i],
                                    "Animal": perm_animals[i],
                                    "Birthday": perm_birthdays[i]
                                }
                                houses.append(house)
                            # Check constraints.
                            if satisfies_constraints(houses):
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

    # Prepare the output in the required JSON format.
    if solution:
        output = {
            "solution": {
                "header": ["House", "Name", "Drink", "Vacation", "House Style", "Animal", "Birthday"],
                "rows": [
                    [house["House"], house["Name"], house["Drink"], house["Vacation"], house["House Style"], house["Animal"], house["Birthday"]]
                    for house in solution
                ]
            }
        }
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()