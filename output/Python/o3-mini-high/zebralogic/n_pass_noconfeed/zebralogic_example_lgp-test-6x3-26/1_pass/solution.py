#!/usr/bin/env python3
import json
from copy import deepcopy

# Global sets of all possible attribute values
ALL_NAMES = {"Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"}
ALL_HEIGHTS = {"very tall", "tall", "super tall", "average", "very short", "short"}
ALL_PHONES = {"oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"}

# We'll work with 6 houses indexed 0 to 5.
# Predefine fixed values and domain restrictions based on house index.
# For each house, we define allowed domains for name, height, phone.
# Also, we incorporate index-based restrictions:
# House numbering: index 0 = house 1, index 5 = house 6.
# Fixed assignments:
#  - House1 (index0): height = "super tall"
#  - House4 (index3): phone = "google pixel 6"
#  - House5 (index4): height = "very short", phone = "oneplus 9"
#  - House6 (index5): height = "short"
#
# Additional domain restrictions based on clues:
#  - Carol must be the very tall person and uses xiaomi mi 11.
#    Thus, if a house gets Carol then its height must be "very tall" and phone "xiaomi mi 11".
#  - Arnold (if assigned) must have height "tall".
#  - Also, if a house gets height "very tall", then its name must be Carol.
#    if a house gets height "tall", then its name must be Arnold.
#  - Eric must be in one of houses 1,2,3 (indexes 0,1,2) because
#    the person with "google pixel 6" (house4, index3) must be to the right of Eric.
#  - Carol cannot be in house1, house4 or house6 because their fixed or constrained heights don't match.
#    So Carol is allowed only in houses with index 1 or 2.
#  - The Samsung Galaxy S21 is not in house1 (index 0).
#  - The person who uses OnePlus 9 is directly left of the person who is short.
#    (We already fix house5's phone as "oneplus 9" and house6's height as "short".)
#  - "Peter is somewhere to the left of the person who uses an iPhone 13" is an ordering rule.
#  - "Bob is directly left of the person who is tall" combined with "the person who is tall is Arnold"
#    forces that Bob is immediately to the left of Arnold.
#
# Based on the above, here are our domain restrictions per house:

domains = []

# House index 0 (House 1)
dom_name_0 = {"Alice", "Eric", "Bob", "Peter", "Arnold"}  # Carol not allowed because super tall doesn't match her "very tall"
dom_height_0 = {"super tall"}  # fixed by clue 9.
# For phones of house 1: cannot be "samsung galaxy s21" and cannot be ones fixed later.
dom_phone_0 = {"iphone 13", "huawei p50"}  # xiaomi mi 11 not allowed because Carol (if it were, her height would need to be "very tall")
domains.append({"name": dom_name_0, "height": dom_height_0, "phone": dom_phone_0})

# House index 1 (House 2)
# Names: all possible
dom_name_1 = {"Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"}
# Heights: not fixed; available from remaining if not fixed – only houses 1-3 (indices 1,2,3) get from {"tall", "very tall", "average"}
dom_height_1 = {"tall", "very tall", "average"}
dom_phone_1 = {"samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"}
domains.append({"name": dom_name_1, "height": dom_height_1, "phone": dom_phone_1})

# House index 2 (House 3)
dom_name_2 = {"Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"}
dom_height_2 = {"tall", "very tall", "average"}
dom_phone_2 = {"samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"}
domains.append({"name": dom_name_2, "height": dom_height_2, "phone": dom_phone_2})

# House index 3 (House 4)
# Eric is not allowed here because google pixel 6 must be to the right of Eric.
dom_name_3 = {"Alice", "Bob", "Peter", "Arnold"}  # Carol excluded because if Carol then phone must be xiaomi mi 11
dom_height_3 = {"tall", "very tall", "average"}
# Phone is fixed
dom_phone_3 = {"google pixel 6"}
domains.append({"name": dom_name_3, "height": dom_height_3, "phone": dom_phone_3})

# House index 4 (House 5)
dom_name_4 = {"Alice", "Bob", "Peter", "Arnold"}  # Eric and Carol not allowed (height conflict with fixed "very short")
dom_height_4 = {"very short"}  # fixed by clue 3 and deduction.
dom_phone_4 = {"oneplus 9"}   # fixed by clue 7.
domains.append({"name": dom_name_4, "height": dom_height_4, "phone": dom_phone_4})

# House index 5 (House 6)
# Eric, Carol, and Arnold are not allowed here.
dom_name_5 = {"Alice", "Bob", "Peter"}
dom_height_5 = {"short"}  # fixed by clue 12.
# For phone of house6, xiaomi mi 11 is disallowed because that would force Carol and height conflict.
dom_phone_5 = {"samsung galaxy s21", "iphone 13", "huawei p50"}
domains.append({"name": dom_name_5, "height": dom_height_5, "phone": dom_phone_5})


# Constraint check for a single house assignment: Check local consistency for a house based on its own triple.
def check_local_constraint(house, index):
    name = house["name"]
    height = house["height"]
    phone = house["phone"]
    # If the house has Carol, then height must be "very tall" and phone must be "xiaomi mi 11".
    if name == "Carol":
        if height != "very tall" or phone != "xiaomi mi 11":
            return False
    # Conversely, if height is "very tall" then the person must be Carol.
    if height == "very tall" and name != "Carol":
        return False
    # If the house has Arnold, then height must be "tall".
    if name == "Arnold":
        if height != "tall":
            return False
    # Conversely, if height is "tall", then the person must be Arnold.
    if height == "tall" and name != "Arnold":
        return False
    # If the house has phone "xiaomi mi 11", then name must be Carol.
    if phone == "xiaomi mi 11" and name != "Carol":
        return False
    # If the house has Carol, phone must be "xiaomi mi 11". (Already checked above)
    return True

# Check cross-house constraints based on the current partial assignment.
def check_cross_house(assignment):
    n = len(assignment)
    # Constraint: Bob is directly left of the person who is tall (which is Arnold).
    for i in range(n):
        if assignment[i]["name"] == "Bob":
            if i + 1 < n:
                if assignment[i+1]["name"] != "Arnold":
                    return False
        if assignment[i]["name"] == "Arnold":
            if i - 1 >= 0:
                if assignment[i-1]["name"] != "Bob":
                    return False

    # Constraint: Peter is somewhere to the left of the person who uses an iPhone 13.
    # If both a house with name "Peter" and a house with phone "iphone 13" are assigned, then index(Peter) must be less than index(iPhone 13).
    peter_index = None
    iphone_index = None
    for idx, house in enumerate(assignment):
        if house["name"] == "Peter":
            peter_index = idx
        if house["phone"] == "iphone 13":
            iphone_index = idx
    if peter_index is not None and iphone_index is not None:
        if not (peter_index < iphone_index):
            return False

    # Constraint: The person who uses Google Pixel 6 (which is fixed at index3) is somewhere to right of Eric.
    # So if Eric is assigned in any house, his index must be less than 3 (since house index3 is the only one with google pixel 6).
    for idx, house in enumerate(assignment):
        if house["name"] == "Eric":
            if idx >= 3:
                return False

    return True

# Backtracking search for a complete valid assignment.
def backtrack(index, assignment, used_names, used_heights, used_phones):
    if index == 6:
        # All houses assigned, check global cross-house constraints one more time.
        if check_cross_house(assignment):
            return assignment
        return None

    # Get domains for current house index.
    curr_domain = domains[index]
    possible_names = curr_domain["name"] - used_names
    possible_heights = curr_domain["height"] - used_heights
    possible_phones = curr_domain["phone"] - used_phones

    # Try all possible combinations for the attributes of current house.
    for name in possible_names:
        for height in possible_heights:
            for phone in possible_phones:
                house = {"name": name, "height": height, "phone": phone}
                # Check local constraints for this house.
                if not check_local_constraint(house, index):
                    continue

                # Create a tentative assignment.
                new_assignment = assignment + [house]
                # Check cross-house constraints with the new assignment.
                if not check_cross_house(new_assignment):
                    continue

                # Update used sets for global uniqueness.
                new_used_names = used_names | {name}
                new_used_heights = used_heights | {height}
                new_used_phones = used_phones | {phone}

                # Recurse to next house.
                result = backtrack(index + 1, new_assignment, new_used_names, new_used_heights, new_used_phones)
                if result is not None:
                    return result
    return None

def solve_puzzle():
    # Initialize used sets with fixed assignments from domains that are fixed.
    # For houses with fixed values, they are already enforced by reducing domain.
    # We'll start with index 0 and empty used sets.
    solution = backtrack(0, [], set(), set(), set())
    return solution

def main():
    solution_assignment = solve_puzzle()
    if solution_assignment is None:
        result = {"solution": {"header": ["House", "Name", "Height", "PhoneModel"], "rows": []}}
    else:
        # Prepare rows in order, house numbers from 1 to 6 as strings.
        rows = []
        for i, house in enumerate(solution_assignment):
            row = [str(i+1), house["name"], house["height"], house["phone"]]
            rows.append(row)
        result = {"solution": {"header": ["House", "Name", "Height", "PhoneModel"], "rows": rows}}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()