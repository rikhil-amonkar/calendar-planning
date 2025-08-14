#!/usr/bin/env python3
import json
from itertools import permutations
import sys

# Global lists for each attribute
NAMES = ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"]
PHONES = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
CIGARS = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
FLOWERS = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
COLORS = ["yellow", "red", "green", "blue", "white", "purple"]
SPORTS = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]

# The order in which we assign categories
ORDER = ["names", "phones", "cigars", "flowers", "colors", "sports"]

def search(level, assignment):
    # When all categories are assigned, we have a complete solution.
    if level == len(ORDER):
        return assignment

    current_category = ORDER[level]
    # For each category, try all permutations filtered by fixed constraints that depend on
    # previously assigned categories.
    if current_category == "names":
        # For names, fixed: House 1 must be Alice, and Carol is immediately to the left of Eric.
        for candidate in permutations(NAMES):
            if candidate[0] != "Alice":
                continue
            # Carol must be immediately left of Eric.
            if candidate.index("Carol") + 1 != candidate.index("Eric"):
                continue
            new_assignment = assignment.copy()
            new_assignment["names"] = candidate
            res = search(level + 1, new_assignment)
            if res is not None:
                return res

    elif current_category == "phones":
        names_assgn = assignment["names"]
        # Fixed: oneplus 9 is in house 2 (index 1).
        # Also: the person who loves blue (Peter) uses iphone 13.
        # And: xiaomi mi 11 is to the left of huawei p50.
        # Also: samsung galaxy s21 is to the left of Eric.
        # And: google pixel 6 is to the right of Eric.
        for candidate in permutations(PHONES):
            if candidate[1] != "oneplus 9":
                continue
            ix_peter = names_assgn.index("Peter")
            if candidate[ix_peter] != "iphone 13":
                continue
            if candidate.index("xiaomi mi 11") >= candidate.index("huawei p50"):
                continue
            ix_eric = names_assgn.index("Eric")
            if candidate.index("samsung galaxy s21") >= ix_eric:
                continue
            if candidate.index("google pixel 6") <= ix_eric:
                continue
            new_assignment = assignment.copy()
            new_assignment["phones"] = candidate
            res = search(level + 1, new_assignment)
            if res is not None:
                return res

    elif current_category == "cigars":
        names_assgn = assignment["names"]
        # Fixed: Peter smokes dunhill and Eric smokes blends.
        for candidate in permutations(CIGARS):
            if candidate[names_assgn.index("Peter")] != "dunhill":
                continue
            if candidate[names_assgn.index("Eric")] != "blends":
                continue
            new_assignment = assignment.copy()
            new_assignment["cigars"] = candidate
            res = search(level + 1, new_assignment)
            if res is not None:
                return res

    elif current_category == "flowers":
        names_assgn = assignment["names"]
        phones_assgn = assignment["phones"]
        # Fixed: Carol loves carnations and Bob loves tulips.
        for candidate in permutations(FLOWERS):
            if candidate[names_assgn.index("Carol")] != "carnations":
                continue
            if candidate[names_assgn.index("Bob")] != "tulips":
                continue
            # There are two houses between Carol and the person who loves daffodils.
            if abs(candidate.index("daffodils") - names_assgn.index("Carol")) != 3:
                continue
            # The person who uses a OnePlus 9 (house index 1) and the person who loves roses are next to each other.
            if abs(candidate.index("roses") - 1) != 1:
                continue
            # The person who loves iris is somewhere to the left of Eric.
            if candidate.index("iris") >= names_assgn.index("Eric"):
                continue
            new_assignment = assignment.copy()
            new_assignment["flowers"] = candidate
            res = search(level + 1, new_assignment)
            if res is not None:
                return res

    elif current_category == "colors":
        names_assgn = assignment["names"]
        phones_assgn = assignment["phones"]
        cigars_assgn = assignment["cigars"]
        for candidate in permutations(COLORS):
            # Fixed: The person who loves blue is Peter.
            if candidate[names_assgn.index("Peter")] != "blue":
                continue
            # The person who uses a Huawei P50 is directly left of the person who loves white.
            ix_huawei = phones_assgn.index("huawei p50")
            if ix_huawei == 5:
                continue
            if candidate[ix_huawei + 1] != "white":
                continue
            # The person who loves yellow and the one who loves blue are next to each other.
            if abs(candidate.index("yellow") - candidate.index("blue")) != 1:
                continue
            # The person who loves purple is directly left of the person who smokes Pall Mall.
            ix_purple = candidate.index("purple")
            if ix_purple == 5:
                continue
            if cigars_assgn[ix_purple + 1] != "pall mall":
                continue
            # The person whose favorite color is green must be the same who smokes Blue Master.
            if candidate.index("green") != cigars_assgn.index("blue master"):
                continue
            new_assignment = assignment.copy()
            new_assignment["colors"] = candidate
            res = search(level + 1, new_assignment)
            if res is not None:
                return res

    elif current_category == "sports":
        names_assgn = assignment["names"]
        phones_assgn = assignment["phones"]
        cigars_assgn = assignment["cigars"]
        for candidate in permutations(SPORTS):
            # Fixed: Carol loves soccer and Peter loves volleyball.
            if candidate[names_assgn.index("Carol")] != "soccer":
                continue
            if candidate[names_assgn.index("Peter")] != "volleyball":
                continue
            # For the person who loves swimming, they use a Google Pixel 6.
            valid = True
            for i in range(6):
                if candidate[i] == "swimming" and phones_assgn[i] != "google pixel 6":
                    valid = False
                    break
            if not valid:
                continue
            # The Prince smoker loves basketball.
            ix_prince = cigars_assgn.index("prince")
            if candidate[ix_prince] != "basketball":
                continue
            # The person who loves baseball is directly left of the person who smokes Blue Master.
            ix_bm = cigars_assgn.index("blue master")
            if ix_bm == 0:
                continue
            if candidate[ix_bm - 1] != "baseball":
                continue
            # The person who loves volleyball uses an iPhone 13.
            for i in range(6):
                if candidate[i] == "volleyball" and phones_assgn[i] != "iphone 13":
                    valid = False
                    break
            if not valid:
                continue
            new_assignment = assignment.copy()
            new_assignment["sports"] = candidate
            res = search(level + 1, new_assignment)
            if res is not None:
                return res

    return None

def main():
    result = search(0, {})
    if not result:
        sys.exit("No solution found")

    # Build the output structure as specified.
    # Header: ["House", "Name", "phone model", "favorite cigar", "favorite flower", "favorite color", "favorite sport"]
    header = ["House", "Name", "phone model", "favorite cigar", "favorite flower", "favorite color", "favorite sport"]
    rows = []
    # Convert tuples to lists and house numbers to string.
    # The order of houses is maintained from left (house 1) to right (house 6)
    names_list = list(result["names"])
    phones_list = list(result["phones"])
    cigars_list = list(result["cigars"])
    flowers_list = list(result["flowers"])
    colors_list = list(result["colors"])
    sports_list = list(result["sports"])
    for i in range(6):
        row = [str(i+1), names_list[i], phones_list[i], cigars_list[i],
               flowers_list[i], colors_list[i], sports_list[i]]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()