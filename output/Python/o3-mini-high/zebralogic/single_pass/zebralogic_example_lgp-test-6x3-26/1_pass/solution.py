#!/usr/bin/env python3
import json

def generate_candidates_for_house(i, rem_names, rem_heights, rem_phones):
    # Fixed constraints by house index (0-indexed)
    # House 0 (House 1): height must be "super tall"
    # House 3 (House 4): phone must be "google pixel 6"
    # House 4 (House 5): phone must be "oneplus 9" and height must be "very short"
    # House 5 (House 6): height must be "short"
    fixed_height = None
    fixed_phone = None
    if i == 0:
        fixed_height = "super tall"
    if i == 3:
        fixed_phone = "google pixel 6"
    if i == 4:
        fixed_height = "very short"
        fixed_phone = "oneplus 9"
    if i == 5:
        fixed_height = "short"

    for name in rem_names:
        # no fixed name for any house
        candidate_name = name
        for height in rem_heights:
            candidate_height = height
            if fixed_height is not None and candidate_height != fixed_height:
                continue
            for phone in rem_phones:
                candidate_phone = phone
                if fixed_phone is not None and candidate_phone != fixed_phone:
                    continue

                # Enforce intrinsic person-attribute rules:
                # Carol must be very tall and use xiaomi mi 11.
                if candidate_name == "Carol":
                    if candidate_height != "very tall":
                        continue
                    if candidate_phone != "xiaomi mi 11":
                        continue
                # Arnold must be tall.
                if candidate_name == "Arnold":
                    if candidate_height != "tall":
                        continue
                # If height is "very tall", the person must be Carol.
                if candidate_height == "very tall" and candidate_name != "Carol":
                    continue
                # If phone is "xiaomi mi 11", the person must be Carol.
                if candidate_phone == "xiaomi mi 11" and candidate_name != "Carol":
                    continue
                # In House 0, phone cannot be samsung galaxy s21.
                if candidate_phone == "samsung galaxy s21" and i == 0:
                    continue
                # Eric must be to the left of the google pixel 6 house (fixed at house 4, index 3),
                # so Eric can only be in houses 0,1,2.
                if candidate_name == "Eric" and i > 2:
                    continue
                # Peter cannot be in the last house (because someone with iPhone 13 must be to his right).
                if candidate_name == "Peter" and i == 5:
                    continue

                candidate = {
                    "house": str(i+1),
                    "name": candidate_name,
                    "height": candidate_height,
                    "phone": candidate_phone
                }
                yield candidate

def local_check(i, assignment):
    # Checks that involve houses 0..i (assignment list length = i+1)
    # Clue 2: "Peter is somewhere to the left of the person who uses an iPhone 13."
    # For every house with phone "iphone 13", ensure at least one earlier house has name "Peter".
    for idx, house in enumerate(assignment):
        if house["phone"] == "iphone 13":
            if not any(assignment[j]["name"] == "Peter" for j in range(idx)):
                return False
    return True

def final_check(assignment):
    # Final global checks after a complete assignment of 6 houses.

    # Clue 1 and 8 combined: "Bob is directly left of the person who is tall" and "The person who is tall is Arnold."
    tall_indices = [i for i, house in enumerate(assignment) if house["height"] == "tall"]
    if len(tall_indices) != 1:
        return False
    ti = tall_indices[0]
    if assignment[ti]["name"] != "Arnold":
        return False
    if ti == 0:
        return False
    if assignment[ti-1]["name"] != "Bob":
        return False

    # Clue 2: "Peter is somewhere to the left of the person who uses an iPhone 13."
    pos_peter = None
    pos_iphone = None
    for i, house in enumerate(assignment):
        if house["name"] == "Peter":
            pos_peter = i
        if house["phone"] == "iphone 13":
            pos_iphone = i
    if pos_peter is None or pos_iphone is None or pos_peter >= pos_iphone:
        return False

    # Clue 11: "The person who uses a Google Pixel 6 is somewhere to the right of Eric."
    # Google Pixel 6 is fixed at house 4 (index 3) by our assignment.
    eric_index = None
    for i, house in enumerate(assignment):
        if house["name"] == "Eric":
            eric_index = i
            break
    if eric_index is None or eric_index >= 3:
        return False

    # Clue 4: "Carol is the person who is very tall."
    # Check that if Carol appears, her height is very tall, and no other house has "very tall".
    for house in assignment:
        if house["name"] == "Carol":
            if house["height"] != "very tall":
                return False
    for house in assignment:
        if house["height"] == "very tall" and house["name"] != "Carol":
            return False

    # Clue 10: "The person who uses a Xiaomi Mi 11 is Carol."
    for house in assignment:
        if house["phone"] == "xiaomi mi 11" and house["name"] != "Carol":
            return False
        if house["name"] == "Carol" and house["phone"] != "xiaomi mi 11":
            return False

    # Clue 6: "The person who uses a Samsung Galaxy S21 is not in the first house."
    if assignment[0]["phone"] == "samsung galaxy s21":
        return False

    # Clue 7: "The person who uses a OnePlus 9 is directly left of the person who is short."
    # Find the house with phone "oneplus 9" and check that the next house's height is "short".
    idx = None
    for i, house in enumerate(assignment):
        if house["phone"] == "oneplus 9":
            idx = i
            break
    if idx is None or idx == 5:
        return False
    if assignment[idx+1]["height"] != "short":
        return False

    # Clue 5 is automatically satisfied by our fixed assignment:
    # Google Pixel 6 is in house 4 (index 3) and "short" is in house 6 (index 5) so one house lies in between.
    
    return True

def backtrack(i, assignment, rem_names, rem_heights, rem_phones, solutions):
    if i == 6:
        if final_check(assignment):
            solutions.append(assignment)
        return
    for candidate in generate_candidates_for_house(i, rem_names, rem_heights, rem_phones):
        # Check neighbor relationship: if previous house is Bob then this must be Arnold with height "tall".
        if i > 0 and assignment[i-1]["name"] == "Bob":
            if candidate["name"] != "Arnold" or candidate["height"] != "tall":
                continue
        # Also, if this candidate is Arnold in the first house, that's invalid.
        if candidate["name"] == "Arnold" and i == 0:
            continue

        new_assignment = assignment + [candidate]
        new_rem_names = rem_names - {candidate["name"]}
        new_rem_heights = rem_heights - {candidate["height"]}
        new_rem_phones = rem_phones - {candidate["phone"]}
        if not local_check(i, new_assignment):
            continue
        backtrack(i+1, new_assignment, new_rem_names, new_rem_heights, new_rem_phones, solutions)

def main():
    names_all = set(["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"])
    heights_all = set(["very tall", "tall", "super tall", "average", "very short", "short"])
    phones_all = set(["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"])
    solutions = []
    backtrack(0, [], names_all, heights_all, phones_all, solutions)
    if solutions:
        # Use the first found solution.
        sol = solutions[0]
        output = {
            "solution": {
                "header": ["House", "Name", "Height", "PhoneModel"],
                "rows": [[house["house"], house["name"], house["height"], house["phone"]] for house in sol]
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()