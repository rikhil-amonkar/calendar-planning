#!/usr/bin/env python3
import json
import itertools

def valid_solution(houses):
    # houses is a list of 5 dictionaries, each with keys "House", "Name", "Mother", "Height"
    
    # Constraint 11: The person who is very short is in the fifth house.
    if houses[4]["Height"] != "very short":
        return False

    # Constraint 6: The person who is very tall is Arnold.
    for house in houses:
        if house["Name"] == "Arnold" and house["Height"] != "very tall":
            return False
        if house["Height"] == "very tall" and house["Name"] != "Arnold":
            return False

    # Constraint 10: Eric is the person whose mother's name is Kailyn.
    for house in houses:
        if house["Name"] == "Eric" and house["Mother"] != "Kailyn":
            return False
        if house["Mother"] == "Kailyn" and house["Name"] != "Eric":
            return False

    # Constraint 1: Alice is the person whose mother's name is Aniya.
    for house in houses:
        if house["Name"] == "Alice" and house["Mother"] != "Aniya":
            return False
        if house["Mother"] == "Aniya" and house["Name"] != "Alice":
            return False

    # Constraint 3: The person whose mother's name is Janelle is Bob.
    for house in houses:
        if house["Name"] == "Bob" and house["Mother"] != "Janelle":
            return False
        if house["Mother"] == "Janelle" and house["Name"] != "Bob":
            return False

    # Constraint 7: Bob is directly left of the person who has an average height.
    bob_index = None
    for i, house in enumerate(houses):
        if house["Name"] == "Bob":
            bob_index = i
            break
    if bob_index is None or bob_index == 4:
        return False
    if houses[bob_index + 1]["Height"] != "average":
        return False

    # Constraint 2: The person who has an average height is somewhere to the left of the person whose mother's name is Penny.
    avg_index = None
    penny_index = None
    for i, house in enumerate(houses):
        if house["Height"] == "average":
            avg_index = i
        if house["Mother"] == "Penny":
            penny_index = i
    if avg_index is None or penny_index is None or avg_index >= penny_index:
        return False

    # Constraint 5: The person who is short is directly left of Arnold.
    arnold_index = None
    for i, house in enumerate(houses):
        if house["Name"] == "Arnold":
            arnold_index = i
            break
    if arnold_index is None or arnold_index == 0:
        return False
    if houses[arnold_index - 1]["Height"] != "short":
        return False

    # Constraint 9: The person who is very tall is somewhere to the right of the person whose mother's name is Holly.
    holly_index = None
    for i, house in enumerate(houses):
        if house["Mother"] == "Holly":
            holly_index = i
            break
    if holly_index is None or holly_index >= arnold_index:
        return False

    # Constraint 4: Peter is not in the second house.
    if houses[1]["Name"] == "Peter":
        return False

    # Constraint 8: Eric is not in the fifth house.
    if houses[4]["Name"] == "Eric":
        return False

    return True

def solve_puzzle():
    names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    mothers = ["Kailyn", "Janelle", "Aniya", "Penny", "Holly"]
    heights = ["average", "very short", "short", "very tall", "tall"]

    # Try every permutation for names, mothers, heights.
    for perm_names in itertools.permutations(names):
        for perm_mothers in itertools.permutations(mothers):
            for perm_heights in itertools.permutations(heights):
                houses = []
                for i in range(5):
                    house = {
                        "House": str(i+1),
                        "Name": perm_names[i],
                        "Mother": perm_mothers[i],
                        "Height": perm_heights[i]
                    }
                    houses.append(house)
                if valid_solution(houses):
                    return houses
    return None

def main():
    solution = solve_puzzle()
    result = {
        "solution": {
            "header": ["House", "Name", "Mother", "Height"],
            "rows": []
        }
    }
    for house in solution:
        result["solution"]["rows"].append([house["House"], house["Name"], house["Mother"], house["Height"]])
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()