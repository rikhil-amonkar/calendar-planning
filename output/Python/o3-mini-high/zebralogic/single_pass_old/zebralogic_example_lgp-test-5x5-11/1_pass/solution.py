#!/usr/bin/env python3
import json

# Define the constraint-checking function using the partial assignment.
def check_partial(assignment):
    n = len(assignment)
    # Same-house constraints (each house is fully assigned)
    for i, house in enumerate(assignment):
        # Clue 1: The Prince smoker is the Desert smoothie lover.
        if house["cigar"] == "prince" and house["smoothie"] != "desert":
            return False
        if house["smoothie"] == "desert" and house["cigar"] != "prince":
            return False
        # Clue 3: The person who is short smokes blends.
        if house["Height"] == "short" and house["cigar"] != "blends":
            return False
        if house["cigar"] == "blends" and house["Height"] != "short":
            return False
        # Clue 5: The person with average height smokes Dunhill.
        if house["Height"] == "average" and house["cigar"] != "dunhill":
            return False
        if house["cigar"] == "dunhill" and house["Height"] != "average":
            return False
        # Clue 6 & 15: Eric is very tall and uses iPhone 13.
        if house["Name"] == "Eric":
            if house["Height"] != "very tall":
                return False
            if house["phone"] != "iphone 13":
                return False
        if house["Height"] == "very tall" and house["Name"] != "Eric":
            return False
        if house["phone"] == "iphone 13" and house["Name"] != "Eric":
            return False
        # Clue 10 & 11: Bob is the Dunhill smoker with average height and Dragonfruit smoothie.
        if house["Name"] == "Bob":
            if house["cigar"] != "dunhill":
                return False
            if house["Height"] != "average":
                return False
            if house["smoothie"] != "dragonfruit":
                return False
        if house["cigar"] == "dunhill" and house["Name"] != "Bob":
            return False
        if house["smoothie"] == "dragonfruit" and house["Name"] != "Bob":
            return False
        # Clue 13: The person using a Samsung Galaxy S21 is short.
        if house["phone"] == "samsung galaxy s21" and house["Height"] != "short":
            return False
        if house["Height"] == "short" and house["phone"] != "samsung galaxy s21":
            return False
        # Clue 8: Bob is not in the fourth house (house #4, index 3).
        if i == 3 and house["Name"] == "Bob":
            return False

    # Neighbor constraints (only check if a neighbor index exists in the current assignment)
    for i, house in enumerate(assignment):
        # Clue 4: The person with iPhone 13 is directly left of the person who smokes Blue Master.
        if house["phone"] == "iphone 13":
            if i < n - 1:
                if assignment[i+1]["cigar"] != "blue master":
                    return False
            else:
                # If this is the last house in a complete assignment, it's a violation.
                if n == 5:
                    return False
        if house["cigar"] == "blue master":
            if i > 0:
                if assignment[i-1]["phone"] != "iphone 13":
                    return False
            else:
                if n == 5:
                    return False

        # Clue 7: Arnold is directly left of the person who uses a Huawei P50.
        if house["Name"] == "Arnold":
            if i < n - 1:
                if assignment[i+1]["phone"] != "huawei p50":
                    return False
            else:
                if n == 5:
                    return False
        if house["phone"] == "huawei p50":
            if i > 0:
                if assignment[i-1]["Name"] != "Arnold":
                    return False
            else:
                if n == 5:
                    return False

        # Clue 9: Eric is directly left of the person who likes Cherry smoothies.
        if house["Name"] == "Eric":
            if i < n - 1:
                if assignment[i+1]["smoothie"] != "cherry":
                    return False
            else:
                if n == 5:
                    return False
        if house["smoothie"] == "cherry":
            if i > 0:
                if assignment[i-1]["Name"] != "Eric":
                    return False
            else:
                if n == 5:
                    return False

    # Clue 12: The person using iPhone 13 and the person using OnePlus 9 are next to each other.
    iphone_index = None
    oneplus_index = None
    for i, house in enumerate(assignment):
        if house["phone"] == "iphone 13":
            iphone_index = i
        if house["phone"] == "oneplus 9":
            oneplus_index = i
    if iphone_index is not None and oneplus_index is not None:
        if abs(iphone_index - oneplus_index) != 1:
            return False

    # Clue 17: Arnold and the person who is very short are next to each other.
    for i, house in enumerate(assignment):
        if house["Name"] == "Arnold":
            neighbors = []
            if i - 1 >= 0:
                neighbors.append(assignment[i-1]["Height"])
            if i + 1 < n:
                neighbors.append(assignment[i+1]["Height"])
            if neighbors and ("very short" not in neighbors):
                return False
        if house["Height"] == "very short":
            neighbors = []
            if i - 1 >= 0:
                neighbors.append(assignment[i-1]["Name"])
            if i + 1 < n:
                neighbors.append(assignment[i+1]["Name"])
            if neighbors and ("Arnold" not in neighbors):
                return False

    # Global ordering constraints (only enforce if both items are placed)
    # Clue 2: There is one house between Eric and Alice.
    eric_index = None
    alice_index = None
    for i, house in enumerate(assignment):
        if house["Name"] == "Eric":
            eric_index = i
        if house["Name"] == "Alice":
            alice_index = i
    if eric_index is not None and alice_index is not None:
        if abs(eric_index - alice_index) != 2:
            return False

    # Clue 14: There are two houses between the person who is very tall (Eric) and the Dragonfruit smoothie lover (Bob).
    bob_index = None
    for i, house in enumerate(assignment):
        if house["Name"] == "Bob":
            bob_index = i
    if eric_index is not None and bob_index is not None:
        if abs(eric_index - bob_index) != 3:
            return False

    # Clue 16: The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
    desert_index = None
    lime_index = None
    for i, house in enumerate(assignment):
        if house["smoothie"] == "desert":
            desert_index = i
        if house["smoothie"] == "lime":
            lime_index = i
    if desert_index is not None and lime_index is not None:
        if desert_index >= lime_index:
            return False

    return True

# Backtracking search to assign attributes to all 5 houses.
def solve_puzzle():
    names = ["Peter", "Arnold", "Eric", "Bob", "Alice"]
    heights = ["average", "very tall", "very short", "short", "tall"]
    cigars = ["prince", "dunhill", "blends", "pall mall", "blue master"]
    smoothies = ["lime", "cherry", "dragonfruit", "watermelon", "desert"]
    phones = ["oneplus 9", "samsung galaxy s21", "iphone 13", "huawei p50", "google pixel 6"]

    solution = []

    # Recursive backtracking function.
    def backtrack(i, assignment, rem_names, rem_heights, rem_cigars, rem_smoothies, rem_phones):
        if i == 5:
            if check_partial(assignment):
                solution.append(list(assignment))
                return True
            return False
        # Iterate over all possible combinations for house i.
        for name in rem_names:
            for height in rem_heights:
                for cigar in rem_cigars:
                    for smoothie in rem_smoothies:
                        for phone in rem_phones:
                            house = {
                                "House": str(i+1),
                                "Name": name,
                                "Height": height,
                                "cigar": cigar,
                                "smoothie": smoothie,
                                "phone": phone
                            }
                            assignment.append(house)
                            if check_partial(assignment):
                                new_rem_names = rem_names.copy()
                                new_rem_names.remove(name)
                                new_rem_heights = rem_heights.copy()
                                new_rem_heights.remove(height)
                                new_rem_cigars = rem_cigars.copy()
                                new_rem_cigars.remove(cigar)
                                new_rem_smoothies = rem_smoothies.copy()
                                new_rem_smoothies.remove(smoothie)
                                new_rem_phones = rem_phones.copy()
                                new_rem_phones.remove(phone)
                                if backtrack(i+1, assignment, new_rem_names, new_rem_heights, new_rem_cigars, new_rem_smoothies, new_rem_phones):
                                    return True
                            assignment.pop()
        return False

    backtrack(0, [], names, heights, cigars, smoothies, phones)
    if solution:
        return solution[0]
    else:
        return None

def main():
    sol = solve_puzzle()
    if sol is None:
        result = {"solution": {"header": ["House", "Name", "Height", "cigar", "smoothie", "phone"], "rows": []}}
    else:
        rows = []
        # Ensure houses are output in order of their house number.
        # They were built in order, so just iterate.
        for house in sol:
            row = [house["House"], house["Name"], house["Height"], house["cigar"], house["smoothie"], house["phone"]]
            rows.append(row)
        result = {
            "solution": {
                "header": ["House", "Name", "Height", "cigar", "smoothie", "phone"],
                "rows": rows
            }
        }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()