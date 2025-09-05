#!/usr/bin/env python3
import json
import copy

# Define all attributes
NAMES = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
FOODS = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
HEIGHTS = ["tall", "average", "super tall", "very short", "very tall", "short"]
DRINKS = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
PETS = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
PHONES = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"]

# Check constraints on the current partial assignment (houses are 0-indexed)
def valid(assignment):
    n = len(assignment)
    
    # Positional constraints:
    # Clue 3: House2 (index 1) food = "soup"
    if n >= 2:
        if assignment[1]["Food"] != "soup":
            return False
        # Clue 21: The person who is very tall is not in the second house.
        if assignment[1]["Height"] == "very tall":
            return False
    # Clue 1: House3 (index 2) phone = "iphone 13"
    if n >= 3:
        if assignment[2]["PhoneModel"] != "iphone 13":
            return False
    # Clues 10 and 20: The person with a rabbit and the person with a hamster are not in the fifth house (index 4)
    if n >= 5:
        if assignment[4]["Pet"] in ("rabbit", "hamster"):
            return False

    # Check local constraints for each house
    for i, house in enumerate(assignment):
        name = house["Name"]
        food = house["Food"]
        height = house["Height"]
        drink = house["Drink"]
        pet = house["Pet"]
        phone = house["PhoneModel"]

        # Clue 2: Bob is the person who is tall.
        if name == "Bob":
            if height != "tall":
                return False

        # Clue 17: Arnold is very tall and Clue 9: Arnold uses oneplus 9.
        if name == "Arnold":
            if height != "very tall" or phone != "oneplus 9":
                return False

        # Clue 15: Carol uses samsung galaxy s21.
        if name == "Carol":
            if phone != "samsung galaxy s21":
                return False

        # Clues 12 & 13: Alice is super tall and has fish.
        if name == "Alice":
            if height != "super tall" or pet != "fish":
                return False

        # Clue 7: The person who loves grilled cheese is the person who is tall.
        # Uniquely, since Bob is the tall person, grilled cheese must belong to Bob.
        if food == "grilled cheese":
            if name != "Bob" or height != "tall":
                return False
        if height == "tall":
            # Only Bob can be tall so food must be grilled cheese for the tall person.
            if name != "Bob" or food != "grilled cheese":
                return False

        # Clue 6: The person who loves stir fry is the person who likes milk.
        if food == "stir fry" and drink != "milk":
            return False
        if drink == "milk":
            if food != "stir fry":
                return False
            # Clue 26: The person who owns a dog is the person who likes milk.
            if pet != "dog":
                return False

        # Clue 8: The person who uses a Xiaomi Mi 11 is the coffee drinker.
        if phone == "xiaomi mi 11" and drink != "coffee":
            return False
        if drink == "coffee" and phone != "xiaomi mi 11":
            return False

        # Clues 18 & 23: The person who loves spaghetti is the one who uses google pixel 6 and is very short.
        if food == "spaghetti":
            if phone != "google pixel 6" or height != "very short":
                return False
        if phone == "google pixel 6":
            if food != "spaghetti" or height != "very short":
                return False

        # Clue 16: The person who is a pizza lover is the person who is short.
        if food == "pizza":
            if height != "short":
                return False
        if height == "short":
            if food != "pizza":
                return False

        # Clue 14: The tea drinker is directly left of the person who is a pizza lover (checked in adjacent section)

        # Clue 26: Already handled above with milk/dog.

        # Clue 9 & 17 already enforced with Arnold.
        # Clue 15 already enforced with Carol.

    # Check adjacent constraints (houses i and i+1)
    for i in range(n - 1):
        left = assignment[i]
        right = assignment[i + 1]
        # Clue 4: Root beer is directly left of the person who uses a Xiaomi Mi 11.
        if left["Drink"] == "root beer" and right["PhoneModel"] != "xiaomi mi 11":
            return False
        if right["PhoneModel"] == "xiaomi mi 11" and left["Drink"] != "root beer":
            return False
        # Clue 5: The person who uses a Huawei P50 is directly left of the person who loves grilled cheese.
        if left["PhoneModel"] == "huawei p50" and right["Food"] != "grilled cheese":
            return False
        if right["Food"] == "grilled cheese" and left["PhoneModel"] != "huawei p50":
            return False
        # Clue 14: The tea drinker is directly left of the person who is a pizza lover.
        if left["Drink"] == "tea" and right["Food"] != "pizza":
            return False
        if right["Food"] == "pizza" and left["Drink"] != "tea":
            return False
        # Clue 25: The person with fish (Alice) is directly left of Eric.
        if left["Name"] == "Alice" and right["Name"] != "Eric":
            return False
        if right["Name"] == "Eric" and left["Name"] != "Alice":
            return False

    # Cross-house ordering constraints:
    # Clue 11: The person with a pet hamster is somewhere to the right of the person who uses a Google Pixel 6.
    pixel_index = None
    hamster_index = None
    for idx, house in enumerate(assignment):
        if house["PhoneModel"] == "google pixel 6":
            pixel_index = idx
        if house["Pet"] == "hamster":
            hamster_index = idx
    if pixel_index is not None and hamster_index is not None:
        if pixel_index >= hamster_index:
            return False
    # If complete assignment and google pixel 6 is in the last house, then no house can be to its right to hold "hamster"
    if n == 6 and pixel_index is not None and pixel_index == 5:
        return False

    # Clue 24: The person who keeps a pet bird is somewhere to the left of the person who loves spaghetti.
    bird_index = None
    spaghetti_index = None
    for idx, house in enumerate(assignment):
        if house["Pet"] == "bird":
            bird_index = idx
        if house["Food"] == "spaghetti":
            spaghetti_index = idx
    if bird_index is not None and spaghetti_index is not None:
        if bird_index >= spaghetti_index:
            return False

    # Clue 22: The person who is super tall (Alice) is somewhere to the left of Peter.
    alice_index = None
    peter_index = None
    for idx, house in enumerate(assignment):
        if house["Name"] == "Alice":
            alice_index = idx
        if house["Name"] == "Peter":
            peter_index = idx
    if alice_index is not None and peter_index is not None:
        if alice_index >= peter_index:
            return False

    # Clue 19: The boba tea drinker is somewhere to the right of the person who loves soup.
    # We know from Clue 3 that house2 (index 1) is soup.
    for idx, house in enumerate(assignment):
        if house["Drink"] == "boba tea" and idx <= 1:
            return False

    return True

# Backtracking search
def backtrack(i, assignment, avail, solutions):
    if i == 6:
        # Complete assignment reached; check global uniqueness (should be ensured by avail structure) and constraints.
        if valid(assignment):
            solutions.append(copy.deepcopy(assignment))
        return

    # Iterate over all combinations from the available sets for house i
    for name in avail["Name"]:
        for food in avail["Food"]:
            for height in avail["Height"]:
                for drink in avail["Drink"]:
                    for pet in avail["Pet"]:
                        for phone in avail["PhoneModel"]:
                            house = {
                                "Name": name,
                                "Food": food,
                                "Height": height,
                                "Drink": drink,
                                "Pet": pet,
                                "PhoneModel": phone
                            }
                            new_assignment = assignment + [house]
                            if not valid(new_assignment):
                                continue
                            # Prepare new available lists by copying and removing the used values
                            new_avail = {
                                "Name": [x for x in avail["Name"] if x != name],
                                "Food": [x for x in avail["Food"] if x != food],
                                "Height": [x for x in avail["Height"] if x != height],
                                "Drink": [x for x in avail["Drink"] if x != drink],
                                "Pet": [x for x in avail["Pet"] if x != pet],
                                "PhoneModel": [x for x in avail["PhoneModel"] if x != phone],
                            }
                            backtrack(i + 1, new_assignment, new_avail, solutions)
                            # If a solution is found, we can optionally break early.
                            if solutions:
                                return

def main():
    # Set up initial availability for each attribute
    avail = {
        "Name": NAMES[:],
        "Food": FOODS[:],
        "Height": HEIGHTS[:],
        "Drink": DRINKS[:],
        "Pet": PETS[:],
        "PhoneModel": PHONES[:]
    }
    
    solutions = []
    backtrack(0, [], avail, solutions)
    
    if solutions:
        # We'll use the first found solution.
        solution = solutions[0]
        # Prepare JSON output with the exact structure required.
        output = {
            "solution": {
                "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                "rows": []
            }
        }
        # Houses are numbered 1 to 6 (left to right)
        for idx, house in enumerate(solution):
            row = [
                str(idx + 1),
                house["Name"],
                house["Food"],
                house["Height"],
                house["Drink"],
                house["Pet"],
                house["PhoneModel"]
            ]
            output["solution"]["rows"].append(row)
        
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()