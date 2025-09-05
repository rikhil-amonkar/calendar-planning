#!/usr/bin/env python3
import itertools
import json

def check_constraints(houses):
    # Clue 1: There is one house between Eric and the tea drinker.
    pos_eric = None
    pos_tea = None
    for i, house in enumerate(houses):
        if house["Name"] == "Eric":
            pos_eric = i
        if house["Drink"] == "tea":
            pos_tea = i
    if pos_eric is None or pos_tea is None or abs(pos_eric - pos_tea) != 2:
        return False

    # Clue 2: The person who likes milk is the person in a ranch-style home.
    for house in houses:
        if house["Drink"] == "milk" and house["HouseStyle"] != "ranch":
            return False
        if house["HouseStyle"] == "ranch" and house["Drink"] != "milk":
            return False

    # Clue 3: The person with a bachelor's degree is in the second house.
    if houses[1]["Education"] != "bachelor":
        return False

    # Clue 4: The person with a high school diploma is the Dane.
    for house in houses:
        if house["Education"] == "high school" and house["Nationality"] != "dane":
            return False
        if house["Nationality"] == "dane" and house["Education"] != "high school":
            return False

    # Clue 5: The Desert smoothie lover is the Swedish person.
    for house in houses:
        if house["Smoothie"] == "desert" and house["Nationality"] != "swede":
            return False
        if house["Nationality"] == "swede" and house["Smoothie"] != "desert":
            return False

    # Clue 6: The person residing in a Victorian house is not in the first house.
    if houses[0]["HouseStyle"] == "victorian":
        return False

    # Clue 7: The person who likes Cherry smoothies is the person living in a colonial-style house.
    for house in houses:
        if house["Smoothie"] == "cherry" and house["HouseStyle"] != "colonial":
            return False
        if house["HouseStyle"] == "colonial" and house["Smoothie"] != "cherry":
            return False

    # Clue 8: Arnold is somewhere to the right of the person residing in a Victorian house.
    pos_victorian = None
    pos_arnold = None
    for i, house in enumerate(houses):
        if house["HouseStyle"] == "victorian":
            pos_victorian = i
        if house["Name"] == "Arnold":
            pos_arnold = i
    if pos_victorian is None or pos_arnold is None or pos_arnold <= pos_victorian:
        return False

    # Clue 9: The person in a ranch-style home is the person with a high school diploma.
    for house in houses:
        if house["HouseStyle"] == "ranch" and house["Education"] != "high school":
            return False
        if house["Education"] == "high school" and house["HouseStyle"] != "ranch":
            return False

    return True

def solve_puzzle():
    names = ["Eric", "Peter", "Arnold"]
    drinks = ["tea", "water", "milk"]
    nationalities = ["dane", "brit", "swede"]
    educations = ["high school", "associate", "bachelor"]
    house_styles = ["victorian", "colonial", "ranch"]
    smoothies = ["cherry", "watermelon", "desert"]

    for perm_names in itertools.permutations(names):
        for perm_drinks in itertools.permutations(drinks):
            for perm_nations in itertools.permutations(nationalities):
                for perm_educations in itertools.permutations(educations):
                    for perm_styles in itertools.permutations(house_styles):
                        for perm_smoothies in itertools.permutations(smoothies):
                            houses = []
                            for i in range(3):
                                house = {
                                    "House": str(i + 1),
                                    "Name": perm_names[i],
                                    "Drink": perm_drinks[i],
                                    "Nationality": perm_nations[i],
                                    "Education": perm_educations[i],
                                    "HouseStyle": perm_styles[i],
                                    "Smoothie": perm_smoothies[i]
                                }
                                houses.append(house)
                            if check_constraints(houses):
                                return houses
    return None

def main():
    solution = solve_puzzle()
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"], "rows": []}}
    else:
        rows = []
        # Houses are already in order from left (House 1) to right (House 3)
        for house in solution:
            row = [
                house["House"],
                house["Name"],
                house["Drink"],
                house["Nationality"],
                house["Education"],
                house["HouseStyle"],
                house["Smoothie"]
            ]
            rows.append(row)
        output = {
            "solution": {
                "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                "rows": rows
            }
        }
    print(json.dumps(output))

if __name__ == "__main__":
    main()