#!/usr/bin/env python3
import json
import sys

# Domains for each attribute.
domains = {
    "Name": ["Bob", "Arnold", "Alice", "Peter", "Eric"],
    "Hobby": ["cooking", "gardening", "painting", "photography", "knitting"],
    "FavoriteSport": ["swimming", "tennis", "soccer", "baseball", "basketball"],
    "HouseStyle": ["ranch", "craftsman", "victorian", "modern", "colonial"],
    "Children": ["Timothy", "Samantha", "Bella", "Meredith", "Fred"],
    "Height": ["average", "very tall", "very short", "short", "tall"]
}

# The order of keys for assignment.
keys = ["Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"]

# There are 5 houses (index 0->house1, ... index 4->house5)
houses_count = 5

# Set up the list of houses with "House" number pre-assigned as string.
def init_houses():
    houses = []
    for i in range(houses_count):
        # Each house is a dict with a "House" field (using 1-indexed house number).
        houses.append({"House": str(i+1)})
    # Fixed assignments from clues:
    # Clue 2 and 4: The person who is tall is in the second house, and that person is Alice.
    houses[1]["Name"] = "Alice"
    houses[1]["Hobby"] = "gardening"  # Clue 8: gardening is in 2nd house.
    houses[1]["Height"] = "tall"
    # Clue 3 and 16: Peter is directly left of Victorian house, and Peter is very tall.
    # Since clue 20 forces Victorian house to be 5th house, house4 must be Victorian and house3 must be Peter.
    houses[3]["Name"] = "Peter"
    houses[3]["Height"] = "very tall"
    houses[3]["FavoriteSport"] = "baseball"  # Clue 5: very tall -> baseball.
    # Clue 20 and 14: The Victorian house is the fifth house and its child is Fred.
    houses[4]["HouseStyle"] = "victorian"
    houses[4]["Children"] = "Fred"
    return houses

# Check all constraints using the current (possibly partial) assignment in houses.
def check_constraints(houses):
    # Constraint 1: Average height <-> child Meredith.
    for house in houses:
        if "Height" in house and house["Height"] == "average":
            if "Children" in house and house["Children"] != "Meredith":
                return False
        if "Children" in house and house["Children"] == "Meredith":
            if "Height" in house and house["Height"] != "average":
                return False

    # Constraint 2: The person who is tall is in the second house.
    if "Height" in houses[1]:
        if houses[1]["Height"] != "tall":
            return False
    for i, house in enumerate(houses):
        if i != 1 and "Height" in house and house["Height"] == "tall":
            return False

    # Constraint 20: Victorian house is in the fifth house.
    if "HouseStyle" in houses[4]:
        if houses[4]["HouseStyle"] != "victorian":
            return False
    for i, house in enumerate(houses):
        if i != 4 and "HouseStyle" in house and house["HouseStyle"] == "victorian":
            return False

    # Constraint 3: Peter is directly left of the Victorian house.
    # Given house5 is victorian, then house4 must be Peter.
    if "HouseStyle" in houses[4] and houses[4].get("HouseStyle") == "victorian":
        if "Name" in houses[3]:
            if houses[3]["Name"] != "Peter":
                return False
    if "Name" in houses[3] and houses[3].get("Name") == "Peter":
        if "HouseStyle" in houses[4]:
            if houses[4]["HouseStyle"] != "victorian":
                return False

    # Constraint 4: Alice is the person who is tall.
    for house in houses:
        if "Name" in house and house["Name"] == "Alice":
            if "Height" in house and house["Height"] != "tall":
                return False
        if "Height" in house and house["Height"] == "tall":
            if "Name" in house and house["Name"] != "Alice":
                return False

    # Constraint 5: The person who loves baseball is very tall.
    for house in houses:
        if "FavoriteSport" in house and house["FavoriteSport"] == "baseball":
            if "Height" in house and house["Height"] != "very tall":
                return False
        if "Height" in house and house["Height"] == "very tall":
            if "FavoriteSport" in house and house["FavoriteSport"] != "baseball":
                return False

    # Constraint 6: The house with child Meredith and the house with child Timothy are next to each other.
    indices = {}
    for idx, house in enumerate(houses):
        if "Children" in house:
            if house["Children"] in ["Meredith", "Timothy"]:
                indices[house["Children"]] = idx
    if "Meredith" in indices and "Timothy" in indices:
        if abs(indices["Meredith"] - indices["Timothy"]) != 1:
            return False

    # Constraint 7: Bob is the person who paints.
    for house in houses:
        if "Name" in house and house["Name"] == "Bob":
            if "Hobby" in house and house["Hobby"] != "painting":
                return False
        if "Hobby" in house and house["Hobby"] == "painting":
            if "Name" in house and house["Name"] != "Bob":
                return False

    # Constraint 8: The person who enjoys gardening is in the second house.
    if "Hobby" in houses[1]:
        if houses[1]["Hobby"] != "gardening":
            return False
    for i, house in enumerate(houses):
        if i != 1 and "Hobby" in house and house["Hobby"] == "gardening":
            return False

    # Constraint 9: The person who is very short is somewhere to the right of Eric.
    eric_index = None
    for i, house in enumerate(houses):
        if "Name" in house and house["Name"] == "Eric":
            eric_index = i
            break
    if eric_index is not None:
        for i, house in enumerate(houses):
            if "Height" in house and house["Height"] == "very short":
                if i <= eric_index:
                    return False

    # Constraint 10: The person who loves tennis has a child named Samantha.
    for house in houses:
        if "FavoriteSport" in house and house["FavoriteSport"] == "tennis":
            if "Children" in house and house["Children"] != "Samantha":
                return False

    # Constraint 11: The person who loves soccer is not in the first house.
    if "FavoriteSport" in houses[0]:
        if houses[0]["FavoriteSport"] == "soccer":
            return False

    # Constraint 12: In a modern-style house, the child is Samantha.
    for house in houses:
        if "Children" in house and house["Children"] == "Samantha":
            if "HouseStyle" in house and house["HouseStyle"] != "modern":
                return False
        if "HouseStyle" in house and house["HouseStyle"] == "modern":
            if "Children" in house and house["Children"] != "Samantha":
                return False
            if "Hobby" in house and house["Hobby"] != "cooking":
                return False
        # Also if hobby is cooking, we expect modern style (by clue 19)
        if "Hobby" in house and house["Hobby"] == "cooking":
            if "HouseStyle" in house and house["HouseStyle"] != "modern":
                return False

    # Constraint 13: The person in a Craftsman-style house has average height (and thus child Meredith by constraint 1).
    for house in houses:
        if "HouseStyle" in house and house["HouseStyle"] == "craftsman":
            if "Height" in house and house["Height"] != "average":
                return False
            if "Children" in house and house["Children"] != "Meredith":
                return False
        if "Height" in house and house["Height"] == "average":
            if "HouseStyle" in house and house["HouseStyle"] != "craftsman":
                return False

    # Constraint 14: The person whose child is Fred lives in a Victorian house.
    for house in houses:
        if "Children" in house and house["Children"] == "Fred":
            if "HouseStyle" in house and house["HouseStyle"] != "victorian":
                return False

    # Constraint 15: The person who is short loves basketball.
    for house in houses:
        if "Height" in house and house["Height"] == "short":
            if "FavoriteSport" in house and house["FavoriteSport"] != "basketball":
                return False
        if "FavoriteSport" in house and house["FavoriteSport"] == "basketball":
            if "Height" in house and house["Height"] != "short":
                return False

    # Constraint 17: The person in a ranch-style home is somewhere to the left of the person who loves cooking.
    for i, house in enumerate(houses):
        if "HouseStyle" in house and house["HouseStyle"] == "ranch":
            # There must exist some j > i with Hobby == cooking.
            found = False
            for j in range(i+1, len(houses)):
                if "Hobby" in houses[j] and houses[j]["Hobby"] == "cooking":
                    found = True
            # If this house is last, it's impossible.
            if i == len(houses) - 1:
                return False
            # If all houses to the right are already assigned and none is cooking, then fail.
            all_assigned = True
            for j in range(i+1, len(houses)):
                if "Hobby" not in houses[j]:
                    all_assigned = False
                    break
            if all_assigned and not found:
                return False

    # Constraint 18: The person who enjoys knitting and the person who enjoys gardening are next to each other.
    # Gardening is fixed in house 2 (index 1). Its neighbors are house index 0 and 2.
    neighbors = []
    if 0 < len(houses):
        if "Hobby" in houses[0]:
            neighbors.append(houses[0]["Hobby"])
        else:
            neighbors.append(None)
    if len(houses) > 2:
        if "Hobby" in houses[2]:
            neighbors.append(houses[2]["Hobby"])
        else:
            neighbors.append(None)
    # If both neighbors are assigned, one of them must be knitting.
    if all(x is not None for x in neighbors):
        if "knitting" not in neighbors:
            return False

    # Constraint 19 is already covered in constraint 12.

    return True

# Recursive backtracking search.
def search(houses, house_index, attr_index, used):
    if house_index == houses_count:
        # All houses assigned. Final check.
        if check_constraints(houses):
            return True
        return False

    # If we've assigned all attributes for current house, move to next.
    if attr_index == len(keys):
        return search(houses, house_index + 1, 0, used)

    current_key = keys[attr_index]
    # If current house already has a fixed value for this attribute, skip to next attribute.
    if current_key in houses[house_index]:
        # But also register the used value if not already registered.
        val = houses[house_index][current_key]
        if val not in used[current_key]:
            used[current_key].add(val)
        if search(houses, house_index, attr_index + 1, used):
            return True
        # Backtrack: if it wasn't already in used? (No removal necessary for fixed ones.)
        return False

    # Iterate possible values from domain that are not used yet.
    for val in domains[current_key]:
        if val in used[current_key]:
            continue
        # Tentatively assign.
        houses[house_index][current_key] = val
        used[current_key].add(val)

        # Check constraints with current partial assignment.
        if check_constraints(houses):
            if search(houses, house_index, attr_index + 1, used):
                return True

        # Backtrack.
        used[current_key].remove(val)
        del houses[house_index][current_key]
    return False

def main():
    houses = init_houses()
    # Set up used sets for each attribute.
    used = {key: set() for key in keys}
    # Pre-register fixed values.
    for house in houses:
        for key in keys:
            if key in house:
                used[key].add(house[key])
    if not search(houses, 0, 0, used):
        sys.exit("No solution found.")
    # Prepare output structure.
    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
            "rows": []
        }
    }
    # Ensure houses are in order from 1 to 5.
    for house in houses:
        row = [
            house.get("House", ""),
            house.get("Name", ""),
            house.get("Hobby", ""),
            house.get("FavoriteSport", ""),
            house.get("HouseStyle", ""),
            house.get("Children", ""),
            house.get("Height", "")
        ]
        output["solution"]["rows"].append(row)
    # Print output as JSON.
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()