import json

# Define the lists of attributes
NAMES = ["Peter", "Arnold", "Eric", "Bob", "Alice"]
HEIGHTS = ["average", "very tall", "very short", "short", "tall"]
CIGARS = ["prince", "dunhill", "blends", "pall mall", "blue master"]
SMOOTHIES = ["lime", "cherry", "dragonfruit", "watermelon", "desert"]
PHONES = ["oneplus 9", "samsung galaxy s21", "iphone 13", "huawei p50", "google pixel 6"]

def check_global(assignments):
    """
    Check global constraints that involve relative positions among houses.
    assignments: list of house dictionaries in order (index 0 = house 1, etc.)
    """
    pos_eric = None
    pos_alice = None
    pos_bob = None
    pos_arnold = None
    pos_very_short = None
    pos_desert = None
    pos_lime = None
    pos_oneplus = None
    pos_iphone = None

    for i, a in enumerate(assignments):
        if a["Name"] == "Eric":
            pos_eric = i
        if a["Name"] == "Alice":
            pos_alice = i
        if a["Name"] == "Bob":
            pos_bob = i
        if a["Name"] == "Arnold":
            pos_arnold = i
        if a["Height"] == "very short":
            pos_very_short = i
        if a["Smoothie"] == "desert":
            pos_desert = i
        if a["Smoothie"] == "lime":
            pos_lime = i
        if a["PhoneModel"] == "oneplus 9":
            pos_oneplus = i
        if a["PhoneModel"] == "iphone 13":
            pos_iphone = i

    # Clue 2: There is one house between Eric and Alice
    if pos_eric is not None and pos_alice is not None:
        if abs(pos_eric - pos_alice) != 2:
            return False

    # Clue 14: Two houses between Eric (very tall) and Bob (dragonfruit)
    if pos_eric is not None and pos_bob is not None:
        if abs(pos_eric - pos_bob) != 3:
            return False

    # Clue 17: Arnold and the person who is very short are next to each other.
    if pos_arnold is not None and pos_very_short is not None:
        if abs(pos_arnold - pos_very_short) != 1:
            return False

    # Clue 16: The Desert smoothie lover (desert, with prince) is somewhere to the left of the Lime smoothie lover.
    if pos_desert is not None and pos_lime is not None:
        if pos_desert >= pos_lime:
            return False

    # Clue 12: The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
    if pos_iphone is not None and pos_oneplus is not None:
        if abs(pos_iphone - pos_oneplus) != 1:
            return False

    return True

def is_consistent(candidate, idx, houses):
    """
    Check consistency of the candidate for house at position idx with:
      - Self-contained attribute relations.
      - Immediate neighbor constraints from already-assigned houses.
      - Global constraints among houses that have been set.
    houses: list of already assigned houses (for indices 0 to idx-1).
    """
    # Self-contained constraints

    # Clue 6 & 15: Eric is very tall and uses iPhone 13.
    if candidate["Name"] == "Eric":
        if candidate["Height"] != "very tall":
            return False
        if candidate["PhoneModel"] != "iphone 13":
            return False
    if candidate["PhoneModel"] == "iphone 13":
        if candidate["Name"] != "Eric":
            return False

    # Clue 10 & 11: Bob is the Dunhill smoker and Dragonfruit smoothie lover.
    if candidate["Name"] == "Bob":
        if candidate["Cigar"] != "dunhill":
            return False
        if candidate["Smoothie"] != "dragonfruit":
            return False
        if candidate["Height"] != "average":
            return False

    # Clue 5: The person with average height is the Dunhill smoker.
    if candidate["Cigar"] == "dunhill" or candidate["Height"] == "average":
        if not (candidate["Cigar"] == "dunhill" and candidate["Height"] == "average"):
            return False

    # Clue 3: The person who is short is the one who smokes blends.
    # And Clue 13: The person who uses Samsung Galaxy S21 is short.
    # We treat these as bidirectional in this puzzle.
    if candidate["Height"] == "short" or candidate["Cigar"] == "blends" or candidate["PhoneModel"] == "samsung galaxy s21":
        if candidate["Height"] == "short":
            if candidate["Cigar"] != "blends":
                return False
            if candidate["PhoneModel"] != "samsung galaxy s21":
                return False
        if candidate["Cigar"] == "blends":
            if candidate["Height"] != "short":
                return False
        if candidate["PhoneModel"] == "samsung galaxy s21":
            if candidate["Height"] != "short":
                return False

    # Clue 1: The Prince smoker is the Desert smoothie lover.
    if candidate["Cigar"] == "prince" or candidate["Smoothie"] == "desert":
        if candidate["Cigar"] == "prince" and candidate["Smoothie"] != "desert":
            return False
        if candidate["Smoothie"] == "desert" and candidate["Cigar"] != "prince":
            return False

    # Clue 8: Bob is not in the fourth house (house number 4 => index 3)
    if idx == 3 and candidate["Name"] == "Bob":
        return False

    # Clue 4: The iPhone 13 user must be directly left of the Blue Master smoker.
    # Thus, if candidate uses iPhone 13 and is in the last house, it's invalid.
    if candidate["PhoneModel"] == "iphone 13" and idx == 4:
        return False

    # Immediate neighbor constraints
    if idx > 0:
        prev = houses[idx - 1]
        # Clue 4 & 9: If the previous house uses iPhone 13 (Eric) then current house:
        # must have Blue Master cigar (Clue 4) and Cherry smoothie (Clue 9).
        if prev["PhoneModel"] == "iphone 13":
            if candidate["Cigar"] != "blue master":
                return False
            if candidate["Smoothie"] != "cherry":
                return False
        # Clue 7: Arnold is directly left of the person who uses a Huawei P50.
        if prev["Name"] == "Arnold":
            if candidate["PhoneModel"] != "huawei p50":
                return False
    # Also, if current candidate uses Huawei P50 then the house to its left must be Arnold.
    if candidate["PhoneModel"] == "huawei p50":
        if idx == 0:
            return False
        else:
            if houses[idx - 1]["Name"] != "Arnold":
                return False

    # Global constraints among assigned houses
    current_assignments = houses[:idx] + [candidate]
    if not check_global(current_assignments):
        return False

    return True

def solve_recursive(idx, houses, rem_names, rem_heights, rem_cigars, rem_smoothies, rem_phones):
    """
    Backtracking search: assign house at index idx using available remaining
    attributes and check all constraints.
    """
    if idx == 5:
        # All houses assigned. Final check.
        if check_global(houses):
            return houses
        return None

    for name in rem_names:
        for height in rem_heights:
            for cigar in rem_cigars:
                for smoothie in rem_smoothies:
                    for phone in rem_phones:
                        candidate = {
                            "Name": name,
                            "Height": height,
                            "Cigar": cigar,
                            "Smoothie": smoothie,
                            "PhoneModel": phone
                        }
                        if is_consistent(candidate, idx, houses):
                            new_houses = houses + [candidate]
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

                            result = solve_recursive(idx + 1, new_houses, new_rem_names, new_rem_heights, new_rem_cigars, new_rem_smoothies, new_rem_phones)
                            if result is not None:
                                return result
    return None

def main():
    solution = solve_recursive(0, [], NAMES, HEIGHTS, CIGARS, SMOOTHIES, PHONES)
    if solution is not None:
        output = {
            "solution": {
                "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
                "rows": []
            }
        }
        for i, house in enumerate(solution):
            row = [
                str(i + 1),
                house["Name"],
                house["Height"],
                house["Cigar"],
                house["Smoothie"],
                house["PhoneModel"]
            ]
            output["solution"]["rows"].append(row)
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()