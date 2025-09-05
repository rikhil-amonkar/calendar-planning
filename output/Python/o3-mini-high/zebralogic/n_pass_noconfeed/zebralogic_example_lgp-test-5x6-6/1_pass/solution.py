#!/usr/bin/env python3
import json
import itertools
import copy

def check_house(house, index):
    # Clue 1: The stew lover is not in the first house (index 0)
    if house["Food"] == "stew" and index == 0:
        return False

    # Clue 5 & 7: The Samsung Galaxy S21 and doctorate must be in house 3 (index 2)
    if index == 2:
        if house["Phone"] != "samsung galaxy s21":
            return False
        if house["Education"] != "doctorate":
            return False
        if house["Name"] != "Eric":
            return False
        if house["Food"] != "pizza":
            return False
    else:
        if house["Phone"] == "samsung galaxy s21":
            return False

    # Clue 3: The person who enjoys mountain retreats is the person with a bachelor's degree.
    # And Clue 8: The person who loves stir fry is the person with a bachelor's degree.
    if house["Education"] == "bachelor":
        if house["Vacation"] != "mountain":
            return False
        if house["Food"] != "stir fry":
            return False
    if house["Vacation"] == "mountain":
        if house["Education"] != "bachelor":
            return False
    if house["Food"] == "stir fry":
        if house["Education"] != "bachelor":
            return False

    # Clue 6/7/9: The person with a doctorate is Eric and is a pizza lover.
    if house["Education"] == "doctorate":
        if house["Name"] != "Eric":
            return False
        if house["Food"] != "pizza":
            return False
    if house["Name"] == "Eric":
        if house["Education"] != "doctorate":
            return False
    if house["Food"] == "pizza":
        if house["Education"] != "doctorate":
            return False

    # Clue 14 and Clue 16: Arnold uses Google Pixel 6 and loves grilled cheese.
    if house["Phone"] == "google pixel 6":
        if house["Name"] != "Arnold":
            return False
    if house["Name"] == "Arnold":
        if house["Phone"] != "google pixel 6":
            return False
        if house["Food"] != "grilled cheese":
            return False
        # Clue 17: Grilled cheese is not in the fourth house (index 3)
        if index == 3:
            return False
    if house["Food"] == "grilled cheese":
        if house["Name"] != "Arnold":
            return False

    # Clue 12: The person who likes cruises is Alice.
    if house["Vacation"] == "cruise":
        if house["Name"] != "Alice":
            return False
    if house["Name"] == "Alice":
        if house["Vacation"] != "cruise":
            return False

    # Clue 11: The person who enjoys camping trips uses an iPhone 13.
    if house["Vacation"] == "camping":
        if house["Phone"] != "iphone 13":
            return False
    if house["Phone"] == "iphone 13":
        if house["Vacation"] != "camping":
            return False

    # Clue 4: The person with a doctorate is to the right of Bob.
    if house["Name"] == "Bob":
        # Since the doctorate is fixed in house index 2, Bob must be in index 0 or 1.
        if index >= 2:
            return False

    # Clue 20: The person whose favorite color is green is not in the second house (index 1).
    if index == 1 and house["Color"] == "green":
        return False

    return True

def check_cross(assignment):
    # assignment is a list of houses (each a dict) with complete attributes.
    n = len(assignment)
    
    # Clue 2: Two houses between the stir fry lover and the person with an associate's degree.
    pos_stir = None
    pos_assoc = None
    for i, house in enumerate(assignment):
        if house["Food"] == "stir fry":
            pos_stir = i
        if house["Education"] == "associate":
            pos_assoc = i
    if pos_stir is not None and pos_assoc is not None:
        if abs(pos_stir - pos_assoc) != 3:
            return False

    # Clue 10: The person whose favorite color is green is somewhere to the right of Peter.
    pos_green = None
    pos_peter = None
    for i, house in enumerate(assignment):
        if house["Color"] == "green":
            pos_green = i
        if house["Name"] == "Peter":
            pos_peter = i
    if pos_green is not None and pos_peter is not None:
        if pos_green <= pos_peter:
            return False

    # Clue 13: There is one house between the person with a high school diploma and the Samsung Galaxy S21.
    # Since Samsung Galaxy S21 is fixed in house index 2, the high school must be in house 0 or 4.
    for i, house in enumerate(assignment):
        if house["Education"] == "high school":
            if abs(i - 2) != 2:
                return False

    # Clue 15: The person who uses a OnePlus 9 is somewhere to the right of the person who uses a Huawei P50.
    pos_oneplus = None
    pos_huawei = None
    for i, house in enumerate(assignment):
        if house["Phone"] == "oneplus 9":
            pos_oneplus = i
        if house["Phone"] == "huawei p50":
            pos_huawei = i
    if pos_oneplus is not None and pos_huawei is not None:
        if pos_oneplus <= pos_huawei:
            return False

    # Clue 18: There are two houses between the bachelor (stir fry lover) and the person whose favorite color is red.
    pos_bachelor = None
    pos_red = None
    for i, house in enumerate(assignment):
        if house["Education"] == "bachelor":
            pos_bachelor = i
        if house["Color"] == "red":
            pos_red = i
    if pos_bachelor is not None and pos_red is not None:
        if abs(pos_bachelor - pos_red) != 3:
            return False

    # Clue 19: The person who loves beach vacations is somewhere to the right of the person who prefers city breaks.
    pos_city = None
    pos_beach = None
    for i, house in enumerate(assignment):
        if house["Vacation"] == "city":
            pos_city = i
        if house["Vacation"] == "beach":
            pos_beach = i
    if pos_city is not None and pos_beach is not None:
        if pos_beach <= pos_city:
            return False

    # Clue 21: The person who loves blue is somewhere to the right of Peter.
    pos_blue = None
    pos_peter = None
    for i, house in enumerate(assignment):
        if house["Color"] == "blue":
            pos_blue = i
        if house["Name"] == "Peter":
            pos_peter = i
    if pos_blue is not None and pos_peter is not None:
        if pos_blue <= pos_peter:
            return False

    # Clue 22: There is one house between the person who enjoys camping trips and the person who loves yellow.
    pos_camping = None
    pos_yellow = None
    for i, house in enumerate(assignment):
        if house["Vacation"] == "camping":
            pos_camping = i
        if house["Color"] == "yellow":
            pos_yellow = i
    if pos_camping is not None and pos_yellow is not None:
        if abs(pos_camping - pos_yellow) != 2:
            return False

    return True

def backtrack(index, assignment, avail):
    if index == 5:
        # Full assignment complete, final global check
        if check_cross(assignment):
            return assignment
        else:
            return None

    keys = ["Name", "Vacation", "Education", "Color", "Phone", "Food"]
    # For the current house, iterate over all possible candidate combinations from the available values.
    # For efficiency, convert the available sets to lists.
    candidates = itertools.product(
        list(avail["Name"]),
        list(avail["Vacation"]),
        list(avail["Education"]),
        list(avail["Color"]),
        list(avail["Phone"]),
        list(avail["Food"])
    )
    for cand in candidates:
        cand_dict = {
            "Name": cand[0],
            "Vacation": cand[1],
            "Education": cand[2],
            "Color": cand[3],
            "Phone": cand[4],
            "Food": cand[5]
        }
        # Enforce fixed positions for house index 2 (third house):
        if index == 2:
            if cand_dict["Name"] != "Eric":
                continue
            if cand_dict["Education"] != "doctorate":
                continue
            if cand_dict["Phone"] != "samsung galaxy s21":
                continue
            if cand_dict["Food"] != "pizza":
                continue
        # Check the local (house-specific) constraints.
        if not check_house(cand_dict, index):
            continue

        # Tentatively add this candidate to the assignment.
        new_assignment = assignment + [cand_dict]
        # Check cross-house constraints for the houses already assigned.
        if not check_cross(new_assignment):
            continue

        # Prepare new available sets for next recursion (deep copy)
        new_avail = {k: avail[k].copy() for k in avail}
        valid_choice = True
        for key, val in cand_dict.items():
            if val not in new_avail[key]:
                valid_choice = False
                break
            new_avail[key].remove(val)
        if not valid_choice:
            continue

        result = backtrack(index + 1, new_assignment, new_avail)
        if result is not None:
            return result
    return None

def main():
    # Define initial domains for each category.
    avail = {
        "Name": {"Arnold", "Eric", "Alice", "Bob", "Peter"},
        "Vacation": {"mountain", "city", "cruise", "beach", "camping"},
        "Education": {"doctorate", "high school", "bachelor", "associate", "master"},
        "Color": {"blue", "red", "white", "yellow", "green"},
        "Phone": {"google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"},
        "Food": {"grilled cheese", "stir fry", "pizza", "spaghetti", "stew"}
    }
    
    solution = backtrack(0, [], avail)
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"], "rows": []}}
    else:
        # Sort the solution by house index (assignment order corresponds to house order 0 to 4)
        rows = []
        for i, house in enumerate(solution):
            row = [
                str(i + 1),
                house["Name"],
                house["Vacation"],
                house["Education"],
                house["Color"],
                house["Phone"],
                house["Food"]
            ]
            rows.append(row)
        output = {"solution": {"header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"], "rows": rows}}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()