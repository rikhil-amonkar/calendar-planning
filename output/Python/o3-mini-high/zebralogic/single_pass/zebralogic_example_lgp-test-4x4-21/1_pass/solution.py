#!/usr/bin/env python3
import itertools
import json

def is_valid(houses):
    # Constraint 1: The person whose birthday is in January ("jan") is not in the second house.
    if houses[1]["birthday"] == "jan":
        return False

    # Constraint 11: Peter is the person whose birthday is in January.
    for house in houses:
        if house["Name"] == "Peter" and house["birthday"] != "jan":
            return False
        if house["birthday"] == "jan" and house["Name"] != "Peter":
            return False

    # Constraint 8: The person who owns a Toyota Camry is Peter.
    for house in houses:
        if house["car"] == "toyota camry" and house["Name"] != "Peter":
            return False
        if house["Name"] == "Peter" and house["car"] != "toyota camry":
            return False

    # Constraint 9: The person whose birthday is in April is Arnold.
    for house in houses:
        if house["birthday"] == "april" and house["Name"] != "Arnold":
            return False
        if house["Name"] == "Arnold" and house["birthday"] != "april":
            return False

    # Constraint 6: The person who owns a Tesla Model 3 is Arnold.
    for house in houses:
        if house["car"] == "tesla model 3" and house["Name"] != "Arnold":
            return False
        if house["Name"] == "Arnold" and house["car"] != "tesla model 3":
            return False

    # Constraint 10: Alice is the photography enthusiast.
    for house in houses:
        if house["Name"] == "Alice" and house["hobby"] != "photography":
            return False
        if house["hobby"] == "photography" and house["Name"] != "Alice":
            return False

    # Constraint 7: The person whose birthday is in February is the person who loves cooking.
    for house in houses:
        if house["birthday"] == "feb" and house["hobby"] != "cooking":
            return False
        if house["hobby"] == "cooking" and house["birthday"] != "feb":
            return False

    # Constraints 2 and 3: The photography enthusiast (Alice) is somewhere to the left of Eric and Peter.
    posAlice = None
    posEric = None
    posPeter = None
    for i, house in enumerate(houses):
        if house["Name"] == "Alice":
            posAlice = i
        if house["Name"] == "Eric":
            posEric = i
        if house["Name"] == "Peter":
            posPeter = i
    if posAlice is None or posEric is None or posPeter is None:
        return False
    if posAlice >= posEric:
        return False
    if posAlice >= posPeter:
        return False

    # Constraint 4: The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
    pair_found = False
    for i in range(len(houses) - 1):
        if houses[i]["car"] == "honda civic" and houses[i+1]["car"] == "tesla model 3":
            pair_found = True
            break
    if not pair_found:
        return False

    # Constraint 5: There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
    index_tesla = None
    index_gardening = None
    for i, house in enumerate(houses):
        if house["car"] == "tesla model 3":
            index_tesla = i
        if house["hobby"] == "gardening":
            index_gardening = i
    if index_tesla is None or index_gardening is None or abs(index_tesla - index_gardening) != 2:
        return False

    return True

def main():
    names = ["Eric", "Peter", "Alice", "Arnold"]
    cars = ["tesla model 3", "honda civic", "toyota camry", "ford f150"]
    birthdays = ["jan", "april", "sept", "feb"]
    hobbies = ["painting", "cooking", "gardening", "photography"]

    solution = None

    for name_perm in itertools.permutations(names):
        for car_perm in itertools.permutations(cars):
            for birthday_perm in itertools.permutations(birthdays):
                for hobby_perm in itertools.permutations(hobbies):
                    houses = []
                    for i in range(4):
                        house = {
                            "House": str(i + 1),
                            "Name": name_perm[i],
                            "car": car_perm[i],
                            "birthday": birthday_perm[i],
                            "hobby": hobby_perm[i]
                        }
                        houses.append(house)
                    if is_valid(houses):
                        solution = houses
                        break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    if solution:
        # Ensure the houses are sorted by their house number
        sorted_solution = sorted(solution, key=lambda h: int(h["House"]))
        output = {
            "solution": {
                "header": ["House", "Name", "car", "birthday", "hobby"],
                "rows": [
                    [house["House"], house["Name"], house["car"], house["birthday"], house["hobby"]]
                    for house in sorted_solution
                ]
            }
        }
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": {}}))

if __name__ == "__main__":
    main()