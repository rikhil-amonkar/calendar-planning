#!/usr/bin/env python3
import itertools
import json

def satisfies_constraints(houses):
    # houses is a list of dictionaries corresponding to house positions 0,1,2.
    n = len(houses)
    
    # Constraint 1:
    # The person who keeps horses and the photography enthusiast are next to each other.
    index_horse = None
    index_photography = None
    for i, house in enumerate(houses):
        if house["Animal"] == "horse":
            index_horse = i
        if house["Hobby"] == "photography":
            index_photography = i
    if index_horse is None or index_photography is None or abs(index_horse - index_photography) != 1:
        return False

    # Constraint 2:
    # The bird keeper is the person who likes Cherry smoothies.
    for house in houses:
        # They must be paired: bird <-> cherry.
        if house["Animal"] == "bird" and house["Smoothie"] != "cherry":
            return False
        if house["Smoothie"] == "cherry" and house["Animal"] != "bird":
            return False

    # Constraint 3 and 6:
    # The person who loves cooking is the Desert smoothie lover and the person who loves a bouquet of daffodils is the Desert smoothie lover.
    # So cooking, desert smoothie, and daffodils must all belong to the same person.
    for house in houses:
        if house["Hobby"] == "cooking":
            if house["Smoothie"] != "desert" or house["Flower"] != "daffodils":
                return False
        if house["Smoothie"] == "desert":
            if house["Hobby"] != "cooking" or house["Flower"] != "daffodils":
                return False

    # Constraint 4:
    # The person who enjoys gardening is the person who loves a carnations arrangement.
    for house in houses:
        if house["Hobby"] == "gardening":
            if house["Flower"] != "carnations":
                return False
        if house["Flower"] == "carnations":
            if house["Hobby"] != "gardening":
                return False

    # Constraint 5:
    # The person who loves cooking is directly left of Peter.
    # Find the house with cooking and ensure the neighbor to the right is Peter.
    found_cooking_before_peter = False
    for i in range(n - 1):
        if houses[i]["Hobby"] == "cooking" and houses[i+1]["Name"] == "Peter":
            found_cooking_before_peter = True
            break
    if not found_cooking_before_peter:
        return False

    # Constraint 7:
    # The Watermelon smoothie lover is the person who keeps horses.
    for house in houses:
        if house["Smoothie"] == "watermelon" and house["Animal"] != "horse":
            return False
        if house["Animal"] == "horse" and house["Smoothie"] != "watermelon":
            return False

    # Constraint 8:
    # The photography enthusiast is Eric.
    for house in houses:
        if house["Hobby"] == "photography" and house["Name"] != "Eric":
            return False
        if house["Name"] == "Eric" and house["Hobby"] != "photography":
            return False

    return True

def solve_puzzle():
    names = ["Eric", "Peter", "Arnold"]
    smoothies = ["cherry", "watermelon", "desert"]
    flowers = ["carnations", "lilies", "daffodils"]
    animals = ["cat", "horse", "bird"]
    hobbies = ["photography", "cooking", "gardening"]

    # There are 3 houses: index 0 => House "1", index 1 => House "2", index 2 => House "3"
    for perm_names in itertools.permutations(names):
        for perm_smoothies in itertools.permutations(smoothies):
            for perm_flowers in itertools.permutations(flowers):
                for perm_animals in itertools.permutations(animals):
                    for perm_hobbies in itertools.permutations(hobbies):
                        houses = []
                        for i in range(3):
                            house = {
                                "House": str(i+1),
                                "Name": perm_names[i],
                                "Smoothie": perm_smoothies[i],
                                "Flower": perm_flowers[i],
                                "Animal": perm_animals[i],
                                "Hobby": perm_hobbies[i]
                            }
                            houses.append(house)
                        
                        if satisfies_constraints(houses):
                            return houses
    return None

if __name__ == '__main__':
    solution_houses = solve_puzzle()
    if not solution_houses:
        output = {"solution": {"header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"], "rows": []}}
    else:
        # Ensure houses are sorted by house number (which are "1", "2", "3")
        solution_houses.sort(key=lambda x: int(x["House"]))
        rows = []
        for house in solution_houses:
            rows.append([house["House"], house["Name"], house["Smoothie"], house["Flower"], house["Animal"], house["Hobby"]])
        output = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                "rows": rows
            }
        }
    print(json.dumps(output))