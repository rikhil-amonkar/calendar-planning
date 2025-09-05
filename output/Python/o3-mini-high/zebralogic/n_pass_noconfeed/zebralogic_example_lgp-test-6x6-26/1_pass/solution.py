#!/usr/bin/env python3
import itertools
import json

# Define all attribute categories.
NAMES = {"Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"}
PHONES = {"huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"}
CIGARS = {"dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"}
FLOWERS = {"daffodils", "carnations", "roses", "tulips", "lilies", "iris"}
COLORS = {"yellow", "red", "green", "blue", "white", "purple"}
SPORTS = {"soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"}

# Final check on a complete assignment.
def final_check(assignment):
    # assignment is list of 6 dicts.
    # Constraint 2: Xiaomi Mi 11 is somewhere to the left of Huawei P50.
    idx_xiaomi = None
    idx_huawei = None
    for i, house in enumerate(assignment):
        if house["PhoneModel"] == "xiaomi mi 11":
            idx_xiaomi = i
        if house["PhoneModel"] == "huawei p50":
            idx_huawei = i
    if idx_xiaomi is not None and idx_huawei is not None:
        if not (idx_xiaomi < idx_huawei):
            return False

    # Constraint 7: Eric is somewhere to the right of Samsung Galaxy S21.
    idx_eric = None
    idx_samsung = None
    for i, house in enumerate(assignment):
        if house["Name"] == "Eric":
            idx_eric = i
        if house["PhoneModel"] == "samsung galaxy s21":
            idx_samsung = i
    if idx_eric is not None and idx_samsung is not None:
        if not (idx_samsung < idx_eric):
            return False

    # Constraint 8: There are exactly two houses between Carol and daffodils.
    idx_carol = None
    idx_daffodils = None
    for i, house in enumerate(assignment):
        if house["Name"] == "Carol":
            idx_carol = i
        if house["Flower"] == "daffodils":
            idx_daffodils = i
    if idx_carol is not None and idx_daffodils is not None:
        if abs(idx_carol - idx_daffodils) != 3:
            return False

    # Constraint 12: The person using Huawei P50 is directly left of the person who loves white.
    for i, house in enumerate(assignment):
        if house["PhoneModel"] == "huawei p50":
            if i == 5:
                return False
            if assignment[i+1]["Color"] != "white":
                return False

    # Constraint 13: The OnePlus 9 (in house 2) and the person who loves roses are next to each other.
    # House 2 is index 1 and fixed. So check neighbors of house index 1:
    neighbors = []
    if 1 - 1 >= 0:
        neighbors.append(assignment[0])
    if 1 + 1 < 6:
        neighbors.append(assignment[2])
    if not any(h["Flower"] == "roses" for h in neighbors):
        return False

    # Constraint 14: The person who loves iris is somewhere to the left of Eric.
    idx_iris = None
    idx_eric = None
    for i, house in enumerate(assignment):
        if house["Flower"] == "iris":
            idx_iris = i
        if house["Name"] == "Eric":
            idx_eric = i
    if idx_iris is not None and idx_eric is not None:
        if not (idx_iris < idx_eric):
            return False

    # Constraint 19: The person who loves baseball is directly left of the person who smokes Blue Master.
    for i, house in enumerate(assignment):
        if house["FavoriteSport"] == "baseball":
            if i == 5:
                return False
            if assignment[i+1]["Cigar"] != "blue master":
                return False

    # Constraint 20: The person using Google Pixel 6 is somewhere to the right of the person who smokes blends.
    idx_google = None
    idx_blends = None
    for i, house in enumerate(assignment):
        if house["PhoneModel"] == "google pixel 6":
            idx_google = i
        if house["Cigar"] == "blends":
            idx_blends = i
    if idx_google is not None and idx_blends is not None:
        if not (idx_google > idx_blends):
            return False

    # Constraint for yellow and blue being next to each other.
    idx_blue = None
    idx_yellow = None
    for i, house in enumerate(assignment):
        if house["Color"] == "blue":
            idx_blue = i
        if house["Color"] == "yellow":
            idx_yellow = i
    if idx_blue is not None and idx_yellow is not None:
        if abs(idx_blue - idx_yellow) != 1:
            return False

    return True

# Partial check on a growing assignment.
def valid_partial(assignment, remaining):
    n = len(assignment)
    for i, house in enumerate(assignment):
        # Carol must be immediately followed by Eric.
        if house["Name"] == "Carol":
            if i == n - 1:
                # If complete assignment then violation.
                if n == 6:
                    return False
                # Otherwise, ensure "Eric" is still available.
                if "Eric" not in remaining["Name"]:
                    return False
            else:
                # Next house (if assigned) must be Eric.
                if assignment[i+1] is not None and assignment[i+1]["Name"] != "Eric":
                    return False
        # Eric must have Carol immediately to his left.
        if house["Name"] == "Eric":
            if i == 0:
                return False
            if assignment[i-1] is not None and assignment[i-1]["Name"] != "Carol":
                return False
        # For phone "huawei p50": cannot be in last house and next house must eventually be white.
        if house["PhoneModel"] == "huawei p50":
            if i == 5:
                return False
            if i+1 < n:
                if assignment[i+1] is not None and assignment[i+1].get("Color") is not None:
                    if assignment[i+1]["Color"] != "white":
                        return False
                else:
                    if "white" not in remaining["Color"]:
                        return False
        # Google Pixel 6 cannot be in house 1.
        if house["PhoneModel"] == "google pixel 6":
            if i == 0:
                return False
            # There must be an Eric in an earlier house.
            if not any(assignment[j]["Name"] == "Eric" for j in range(i)):
                return False
        # Samsung Galaxy S21 cannot be in the last house.
        if house["PhoneModel"] == "samsung galaxy s21":
            if i == 5:
                return False
        # Cigar "pall mall" must have the previous house with color purple.
        if house["Cigar"] == "pall mall":
            if i == 0:
                return False
            if assignment[i-1] is not None and assignment[i-1].get("Color") is not None:
                if assignment[i-1]["Color"] != "purple":
                    return False
        # Cigar "blue master" must have the previous house with sport baseball.
        if house["Cigar"] == "blue master":
            if i == 0:
                return False
            if assignment[i-1] is not None and assignment[i-1].get("FavoriteSport") is not None:
                if assignment[i-1]["FavoriteSport"] != "baseball":
                    return False
        # Sport "baseball" must be followed immediately by a house with cigar blue master.
        if house["FavoriteSport"] == "baseball":
            if i == 5:
                return False
            if i+1 < n:
                if assignment[i+1] is not None and assignment[i+1].get("Cigar") is not None:
                    if assignment[i+1]["Cigar"] != "blue master":
                        return False
                else:
                    if "blue master" not in remaining["Cigar"]:
                        return False
        # Color "purple" must be immediately followed by a house with cigar pall mall.
        if house["Color"] == "purple":
            if i == 5:
                return False
            if i+1 < n:
                if assignment[i+1] is not None and assignment[i+1].get("Cigar") is not None:
                    if assignment[i+1]["Cigar"] != "pall mall":
                        return False
    # Check OnePlus 9 (house 2, index 1) neighbor condition for roses.
    if n >= 3:
        if assignment[0] is not None and assignment[2] is not None:
            if assignment[0]["Flower"] != "roses" and assignment[2]["Flower"] != "roses":
                return False
    return True

# Backtracking search; assignment is a list of house dictionaries.
def backtrack(pos, assignment, remaining):
    if pos == 6:
        if final_check(assignment):
            return assignment
        else:
            return None
    # Iterate over all candidate assignments for house number pos.
    # Each candidate is a tuple (Name, PhoneModel, Cigar, Flower, Color, FavoriteSport)
    for candidate in itertools.product(remaining["Name"],
                                       remaining["PhoneModel"],
                                       remaining["Cigar"],
                                       remaining["Flower"],
                                       remaining["Color"],
                                       remaining["FavoriteSport"]):
        cand = {
            "Name": candidate[0],
            "PhoneModel": candidate[1],
            "Cigar": candidate[2],
            "Flower": candidate[3],
            "Color": candidate[4],
            "FavoriteSport": candidate[5]
        }
        # Enforce fixed position constraints.
        if pos == 0 and cand["Name"] != "Alice":
            continue
        if pos == 1 and cand["PhoneModel"] != "oneplus 9":
            continue

        # Enforce forced attribute relationships.
        if cand["Name"] == "Peter":
            if cand["PhoneModel"] != "iphone 13" or cand["Cigar"] != "dunhill" or \
               cand["FavoriteSport"] != "volleyball" or cand["Color"] != "blue":
                continue
        if cand["Name"] == "Carol":
            if cand["Flower"] != "carnations" or cand["FavoriteSport"] != "soccer":
                continue
        if cand["Name"] == "Eric":
            if cand["Cigar"] != "blends":
                continue
        if cand["Name"] == "Bob":
            if cand["Flower"] != "tulips":
                continue
        if cand["PhoneModel"] == "google pixel 6":
            if cand["FavoriteSport"] != "swimming":
                continue
        if cand["FavoriteSport"] == "volleyball":
            if cand["PhoneModel"] != "iphone 13":
                continue
        if cand["Cigar"] == "prince":
            if cand["FavoriteSport"] != "basketball":
                continue
        if cand["FavoriteSport"] == "basketball":
            if cand["Cigar"] != "prince":
                continue
        if cand["Cigar"] == "blends" and cand["Name"] != "Eric":
            continue
        if cand["Cigar"] == "dunhill" and cand["Name"] != "Peter":
            continue
        if cand["Color"] == "blue" and cand["Name"] != "Peter":
            continue
        if cand["Name"] == "Peter" and cand["Color"] != "blue":
            continue
        # Additional phone position constraints.
        if cand["PhoneModel"] == "xiaomi mi 11" and pos == 5:
            continue
        if cand["PhoneModel"] == "samsung galaxy s21" and pos == 5:
            continue
        if cand["PhoneModel"] == "google pixel 6" and pos == 0:
            continue

        new_assignment = assignment + [cand]
        new_remaining = {key: set(remaining[key]) for key in remaining}
        new_remaining["Name"].discard(cand["Name"])
        new_remaining["PhoneModel"].discard(cand["PhoneModel"])
        new_remaining["Cigar"].discard(cand["Cigar"])
        new_remaining["Flower"].discard(cand["Flower"])
        new_remaining["Color"].discard(cand["Color"])
        new_remaining["FavoriteSport"].discard(cand["FavoriteSport"])
        
        if not valid_partial(new_assignment, new_remaining):
            continue

        result = backtrack(pos + 1, new_assignment, new_remaining)
        if result is not None:
            return result
    return None

def main():
    # Set up initial remaining sets.
    remaining = {
        "Name": set(NAMES),
        "PhoneModel": set(PHONES),
        "Cigar": set(CIGARS),
        "Flower": set(FLOWERS),
        "Color": set(COLORS),
        "FavoriteSport": set(SPORTS)
    }
    solution = backtrack(0, [], remaining)
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
                                 "rows": []}}
    else:
        header = ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"]
        rows = []
        for i, house in enumerate(solution):
            row = [str(i+1),
                   house["Name"],
                   house["PhoneModel"],
                   house["Cigar"],
                   house["Flower"],
                   house["Color"],
                   house["FavoriteSport"]]
            rows.append(row)
        output = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()