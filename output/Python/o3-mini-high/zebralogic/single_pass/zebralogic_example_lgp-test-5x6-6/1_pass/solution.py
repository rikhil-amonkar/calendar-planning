#!/usr/bin/env python3
import json
import copy

# Define the attribute lists
names_list = ["Arnold", "Eric", "Alice", "Bob", "Peter"]
vacations_list = ["mountain", "city", "cruise", "beach", "camping"]
educations_list = ["doctorate", "high school", "bachelor", "associate", "master"]
colors_list = ["blue", "red", "white", "yellow", "green"]
phones_list = ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"]
lunches_list = ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]

# The order in which we'll assign attributes for each house.
ordered_keys = ["Name", "education", "phone", "vacation", "lunch", "favorite color"]

# Global domain for each attribute.
domain = {
    "Name": names_list,
    "vacation": vacations_list,
    "education": educations_list,
    "favorite color": colors_list,
    "phone": phones_list,
    "lunch": lunches_list
}

# Forced values for house 3 (index 2)
force_vals = {
    "Name": "Eric",
    "education": "doctorate",
    "phone": "samsung galaxy s21",
    "lunch": "pizza"
}

def local_consistency(assignment, house_index):
    # Check constraints that apply to a single house (local constraints)
    if "Name" in assignment:
        if assignment["Name"] == "Arnold":
            if "phone" in assignment and assignment["phone"] != "google pixel 6":
                return False
            if "lunch" in assignment and assignment["lunch"] != "grilled cheese":
                return False
        if assignment["Name"] == "Alice":
            if "vacation" in assignment and assignment["vacation"] != "cruise":
                return False

    if "education" in assignment:
        if assignment["education"] == "bachelor":
            if "vacation" in assignment and assignment["vacation"] != "mountain":
                return False
            if "lunch" in assignment and assignment["lunch"] != "stir fry":
                return False
        if assignment["education"] == "high school":
            # High school must be in house 1 or house 5 (index 0 or 4)
            if house_index not in [0, 4]:
                return False

    if "vacation" in assignment:
        if assignment["vacation"] == "mountain":
            if "education" in assignment and assignment["education"] != "bachelor":
                return False
        if assignment["vacation"] == "camping":
            if "phone" in assignment and assignment["phone"] != "iphone 13":
                return False

    if "lunch" in assignment:
        if assignment["lunch"] == "stir fry":
            if "education" in assignment and assignment["education"] != "bachelor":
                return False
        if assignment["lunch"] == "grilled cheese":
            # Grilled cheese not allowed in house 4 (index 3)
            if house_index == 3:
                return False
        if assignment["lunch"] == "stew":
            # Stew is not allowed in the first house (index 0)
            if house_index == 0:
                return False

    # For house 3 (index 2), forced assignments:
    if house_index == 2:
        if "Name" in assignment and assignment["Name"] != "Eric":
            return False
        if "education" in assignment and assignment["education"] != "doctorate":
            return False
        if "phone" in assignment and assignment["phone"] != "samsung galaxy s21":
            return False
        if "lunch" in assignment and assignment["lunch"] != "pizza":
            return False

    return True

def assign_house_attributes(house_index, used, current=None, attr_index=0):
    if current is None:
        current = {}
    if attr_index == len(ordered_keys):
        yield current.copy()
        return
    attr = ordered_keys[attr_index]
    # If this is house 3 (index 2) and the attribute has a forced value, restrict candidate.
    if house_index == 2 and attr in force_vals:
        candidate_values = [force_vals[attr]]
    else:
        candidate_values = [val for val in domain[attr] if val not in used[attr]]
    for val in candidate_values:
        current[attr] = val
        if local_consistency(current, house_index):
            yield from assign_house_attributes(house_index, used, current, attr_index + 1)
        del current[attr]

def check_global_partial(houses, num_assigned):
    # Build mappings for the assigned houses only
    # houses[0] to houses[num_assigned-1] are complete.
    # First, check the special condition: The person with doctorate (house 3) is to the right of Bob.
    # Since doctorate is fixed at house 3 (index 2), Bob must appear in house 1 or 2 (indexes 0 or 1).
    if num_assigned >= 2:
        if houses[0]["Name"] != "Bob" and houses[1]["Name"] != "Bob":
            return False

    name_to_index = {}
    vacation_to_index = {}
    education_to_index = {}
    color_to_index = {}
    phone_to_index = {}
    lunch_to_index = {}
    for i in range(num_assigned):
        house = houses[i]
        name_to_index[house["Name"]] = i
        vacation_to_index[house["vacation"]] = i
        education_to_index[house["education"]] = i
        color_to_index[house["favorite color"]] = i
        phone_to_index[house["phone"]] = i
        lunch_to_index[house["lunch"]] = i

    # Constraint 2: Two houses between stir fry and associate.
    if "stir fry" in lunch_to_index and "associate" in education_to_index:
        if abs(lunch_to_index["stir fry"] - education_to_index["associate"]) != 3:
            return False

    # Constraint 10: Favorite color green is somewhere to the right of Peter.
    if "green" in color_to_index and "Peter" in name_to_index:
        if color_to_index["green"] <= name_to_index["Peter"]:
            return False

    # Constraint 13: High school must be in house 1 or house 5 (index 0 or 4)
    if "high school" in education_to_index:
        if education_to_index["high school"] not in [0, 4]:
            return False

    # Constraint 15: OnePlus 9 is somewhere to the right of Huawei P50.
    if "oneplus 9" in phone_to_index and "huawei p50" in phone_to_index:
        if phone_to_index["oneplus 9"] <= phone_to_index["huawei p50"]:
            return False

    # Constraint 18: Two houses between bachelor and red.
    if "bachelor" in education_to_index and "red" in color_to_index:
        if abs(education_to_index["bachelor"] - color_to_index["red"]) != 3:
            return False

    # Constraint 19: Beach vacation is somewhere to the right of city break.
    if "beach" in vacation_to_index and "city" in vacation_to_index:
        if vacation_to_index["beach"] <= vacation_to_index["city"]:
            return False

    # Constraint 20: Green is not in the second house (index 1).
    if "green" in color_to_index:
        if color_to_index["green"] == 1:
            return False

    # Constraint 21: Favorite color blue is somewhere to the right of Peter.
    if "blue" in color_to_index and "Peter" in name_to_index:
        if color_to_index["blue"] <= name_to_index["Peter"]:
            return False

    # Constraint 22: One house between camping vacation and yellow.
    if "camping" in vacation_to_index and "yellow" in color_to_index:
        if abs(vacation_to_index["camping"] - color_to_index["yellow"]) != 2:
            return False

    return True

def check_global(houses):
    # When all 5 houses are assigned, check all global constraints.
    # Build full mappings.
    name_to_index = {}
    vacation_to_index = {}
    education_to_index = {}
    color_to_index = {}
    phone_to_index = {}
    lunch_to_index = {}
    for i, house in enumerate(houses):
        name_to_index[house["Name"]] = i
        vacation_to_index[house["vacation"]] = i
        education_to_index[house["education"]] = i
        color_to_index[house["favorite color"]] = i
        phone_to_index[house["phone"]] = i
        lunch_to_index[house["lunch"]] = i

    # Constraint 2: two houses between stir fry and associate.
    if "stir fry" in lunch_to_index and "associate" in education_to_index:
        if abs(lunch_to_index["stir fry"] - education_to_index["associate"]) != 3:
            return False

    # Constraint 4: The person with a doctorate (house 3, index 2) is to the right of Bob.
    if "Bob" in name_to_index:
        if name_to_index["Bob"] >= 2:
            return False

    # Constraint 10: Green is to the right of Peter.
    if "green" in color_to_index and "Peter" in name_to_index:
        if color_to_index["green"] <= name_to_index["Peter"]:
            return False

    # Constraint 13: High school must be in house 1 or house 5 (index 0 or 4).
    if "high school" in education_to_index:
        if education_to_index["high school"] not in [0, 4]:
            return False

    # Constraint 15: OnePlus 9 is somewhere to the right of Huawei P50.
    if "oneplus 9" in phone_to_index and "huawei p50" in phone_to_index:
        if phone_to_index["oneplus 9"] <= phone_to_index["huawei p50"]:
            return False

    # Constraint 18: Two houses between bachelor and red.
    if "bachelor" in education_to_index and "red" in color_to_index:
        if abs(education_to_index["bachelor"] - color_to_index["red"]) != 3:
            return False

    # Constraint 19: Beach vacation is to the right of city break.
    if "beach" in vacation_to_index and "city" in vacation_to_index:
        if vacation_to_index["beach"] <= vacation_to_index["city"]:
            return False

    # Constraint 20: Green is not in the second house (index 1).
    if "green" in color_to_index:
        if color_to_index["green"] == 1:
            return False

    # Constraint 21: Blue is to the right of Peter.
    if "blue" in color_to_index and "Peter" in name_to_index:
        if color_to_index["blue"] <= name_to_index["Peter"]:
            return False

    # Constraint 22: One house between camping and yellow.
    if "camping" in vacation_to_index and "yellow" in color_to_index:
        if abs(vacation_to_index["camping"] - color_to_index["yellow"]) != 2:
            return False

    return True

def solve_houses(houses, house_index, used):
    if house_index == 5:
        if check_global(houses):
            return houses.copy()
        else:
            return None

    for assignment in assign_house_attributes(house_index, used):
        houses[house_index] = assignment
        new_used = { key: used[key].copy() for key in used }
        for key in ordered_keys:
            new_used[key].add(assignment[key])
        if not check_global_partial(houses, house_index + 1):
            continue
        result = solve_houses(houses, house_index + 1, new_used)
        if result is not None:
            return result
    houses[house_index] = None
    return None

def main():
    # There are 5 houses, indexed 0..4.
    houses = [None] * 5
    used = { key: set() for key in ordered_keys }
    solution = solve_houses(houses, 0, used)
    if solution is None:
        result = {"solution": {"header": ["House", "Name", "vacation", "education", "favorite color", "phone", "lunch"], "rows": []}}
    else:
        rows = []
        for i, house in enumerate(solution):
            row = [
                str(i + 1),
                house["Name"],
                house["vacation"],
                house["education"],
                house["favorite color"],
                house["phone"],
                house["lunch"]
            ]
            rows.append(row)
        result = {"solution": {"header": ["House", "Name", "vacation", "education", "favorite color", "phone", "lunch"], "rows": rows}}
    print(json.dumps(result))

if __name__ == "__main__":
    main()