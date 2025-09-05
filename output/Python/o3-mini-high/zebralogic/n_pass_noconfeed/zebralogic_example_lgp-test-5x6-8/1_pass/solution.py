#!/usr/bin/env python3
import json
import copy

# Define the lists of possible values
NAMES = ["Eric", "Peter", "Arnold", "Bob", "Alice"]
HOUSE_STYLES = ["modern", "craftsman", "ranch", "victorian", "colonial"]
MOTHERS = ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]
PHONE_MODELS = ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"]
DRINKS = ["coffee", "water", "root beer", "tea", "milk"]
ANIMALS = ["fish", "dog", "horse", "bird", "cat"]

# The indices correspond to houses 1 to 5 (0-indexed)
# Some houses have fixed attributes per clues:
# House 3 (index 2): must have HouseStyle "modern", PhoneModel "oneplus 9", Mother "Penny", Animal "horse"
# House 4 (index 3): must have Name "Bob", Drink "tea", Animal "bird"

FIXED = {
    2: {  # House number 3
        "HouseStyle": "modern",
        "PhoneModel": "oneplus 9",
        "Mother": "Penny",
        "Animal": "horse"
    },
    3: {  # House number 4
        "Name": "Bob",
        "Drink": "tea",
        "Animal": "bird"
    }
}

# Helper function: check the local candidate constraints for one house
def valid_local(candidate, index):
    # Enforce water drinker is Alice and mother must be Janelle
    if candidate["Drink"] == "water":
        if candidate["Name"] != "Alice" or candidate["Mother"] != "Janelle":
            return False
    if candidate["Name"] == "Alice":
        if candidate["Drink"] != "water":
            return False
    if candidate["Mother"] == "Janelle":
        if candidate["Drink"] != "water":
            return False

    # Tea drinker must be Bob
    if candidate["Drink"] == "tea" and candidate["Name"] != "Bob":
        return False
    if candidate["Name"] == "Bob":
        if candidate["Drink"] != "tea":
            return False

    # Root beer lover is Peter and must keep a cat
    if candidate["Drink"] == "root beer":
        if candidate["Name"] != "Peter" or candidate["Animal"] != "cat":
            return False
    if candidate["Animal"] == "cat":
        if candidate["Drink"] != "root beer":
            return False

    # Milk drinker gets iphone 13 and a dog
    if candidate["Drink"] == "milk":
        if candidate["PhoneModel"] != "iphone 13" or candidate["Animal"] != "dog":
            return False
    if candidate["PhoneModel"] == "iphone 13":
        if candidate["Drink"] != "milk":
            return False
    if candidate["Animal"] == "dog":
        if candidate["Drink"] != "milk":
            return False

    # google pixel 6 -> craftsman, and cannot be in the first house (index 0)
    if candidate["PhoneModel"] == "google pixel 6":
        if candidate["HouseStyle"] != "craftsman":
            return False
        if index == 0:
            return False

    # Ranch style home -> mother's name is Kailyn
    if candidate["HouseStyle"] == "ranch":
        if candidate["Mother"] != "Kailyn":
            return False

    # Modern-style home -> mother's name is Penny
    if candidate["HouseStyle"] == "modern":
        if candidate["Mother"] != "Penny":
            return False

    # House-specific fixed positions:
    if index == 1 and candidate["Name"] == "Eric":
        # Eric is not in the second house (index 1)
        return False

    if index == 2:
        # House #3 fixed: must be modern, oneplus 9, Penny, and horse.
        if candidate.get("HouseStyle") != "modern" or candidate.get("PhoneModel") != "oneplus 9" \
           or candidate.get("Mother") != "Penny" or candidate.get("Animal") != "horse":
            return False

    if index == 3:
        # House #4 fixed: must be Bob, tea, bird; also mother's can't be Aniya.
        if candidate.get("Name") != "Bob" or candidate.get("Drink") != "tea" or candidate.get("Animal") != "bird":
            return False
        if candidate.get("Mother") == "Aniya":
            return False

    # If animal is horse then houseStyle must be modern and phone must be oneplus 9.
    if candidate["Animal"] == "horse":
        if candidate["HouseStyle"] != "modern" or candidate["PhoneModel"] != "oneplus 9":
            return False

    return True

# Check cross-house (ordering and relational) constraints on the current full or partial assignment.
def check_partial(assignment):
    # assignment is a list of house dictionaries for houses 0..n-1.
    n = len(assignment)
    # Constraint: For any house with phone "huawei p50" and any house with houseStyle "colonial", the huawei house must be to the left.
    huawei_indexes = [i for i, house in enumerate(assignment) if house["PhoneModel"] == "huawei p50"]
    colonial_indexes = [i for i, house in enumerate(assignment) if house["HouseStyle"] == "colonial"]
    for h in huawei_indexes:
        for c in colonial_indexes:
            if h >= c:
                return False

    # Constraint: The tea drinker (should be in house index 3) is to the right of the person whose mother's name is Kailyn.
    tea_indexes = [i for i, house in enumerate(assignment) if house["Drink"] == "tea"]
    kailyn_indexes = [i for i, house in enumerate(assignment) if house["Mother"] == "Kailyn"]
    if tea_indexes and kailyn_indexes:
        for k in kailyn_indexes:
            for t in tea_indexes:
                if k >= t:
                    return False

    # Constraint: The root beer lover (Peter) is to the left of the person whose mother's name is Kailyn.
    rootbeer_indexes = [i for i, house in enumerate(assignment) if house["Drink"] == "root beer"]
    if rootbeer_indexes and kailyn_indexes:
        for r in rootbeer_indexes:
            for k in kailyn_indexes:
                if r >= k:
                    return False

    # Constraint: A colonial-style house is not allowed in house 4 (index 3)
    for i, house in enumerate(assignment):
        if house["HouseStyle"] == "colonial" and i == 3:
            return False

    return True

# Full assignment check when all houses (5) are assigned.
def check_global(assignment):
    # For a full assignment, we also verify that every fixed relational constraint holds.
    if not check_partial(assignment):
        return False

    # Constraint: The person who uses a Google Pixel 6 is not in the first house.
    for i, house in enumerate(assignment):
        if house["PhoneModel"] == "google pixel 6" and i == 0:
            return False

    # Constraint: The one who drinks water is Alice (and vice versa) already handled locally.
    # Constraint: The person living in a colonial-style house is somewhere to the right of the person who uses a Huawei P50.
    # (Already handled in check_partial)
    # Constraint: The person who keeps horses is the person who uses a OnePlus 9 (and modern style, Penny) - handled.
    # Constraint: The person in a ranch-style home is the person whose mother's name is Kailyn - handled.
    # Constraint: The root beer lover is the cat lover - handled.
    # Constraint: The tea drinker is Bob - handled.
    # Constraint: The tea drinker is somewhere to the right of the person whose mother's name is Kailyn - handled.
    # Constraint: The root beer lover is somewhere to the left of the person whose mother's name is Kailyn - handled.
    # Constraint: The person who uses an iPhone 13 is the person who likes milk - handled.
    # Constraint: The dog owner is the person who likes milk - handled.
    # Constraint: The person who uses a Google Pixel 6 is in a Craftsman-style house - handled.
    # Constraint: Eric is not in the second house - handled.
    # Constraint: The person whose mother's name is Aniya is not in the fourth house (index 3) - handled.
    # Constraint: The person whose mother's name is Janelle is the one who only drinks water - handled.
    return True

# Recursive backtracking search over houses 0 to 4.
def search(house_index, assignment, remaining):
    if house_index == 5:
        if check_global(assignment):
            return assignment
        else:
            return None

    # Prepare a candidate dictionary for the current house.
    # For each attribute, if the house index is fixed, then its value is forced.
    fixed_attrs = FIXED.get(house_index, {})

    # Determine which attributes are free for this house.
    attributes = ["Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"]

    # For each attribute, if it is fixed, then candidate value must equal that.
    # We'll loop over the Cartesian product of possibilities for free attributes.
    # To reduce search, generate lists of possible values for each attribute.
    domains = {}
    for attr in attributes:
        if attr in fixed_attrs:
            # Must pick exactly the fixed value if available.
            if fixed_attrs[attr] in remaining[attr]:
                domains[attr] = [fixed_attrs[attr]]
            else:
                return None  # fixed value not available => dead end
        else:
            # Use all remaining possibilities for that attribute.
            domains[attr] = list(remaining[attr])
    
    # If house_index is 2 or 3 (which are fixed houses in some attributes), we only iterate over the free ones.
    # Now iterate over all combinations in the current domain.
    for name in domains["Name"]:
        for style in domains["HouseStyle"]:
            for mother in domains["Mother"]:
                for phone in domains["PhoneModel"]:
                    for drink in domains["Drink"]:
                        for animal in domains["Animal"]:
                            candidate = {
                                "Name": name,
                                "HouseStyle": style,
                                "Mother": mother,
                                "PhoneModel": phone,
                                "Drink": drink,
                                "Animal": animal
                            }
                            # Check local candidate constraints
                            if not valid_local(candidate, house_index):
                                continue

                            # Create new assignment with this house candidate.
                            new_assignment = assignment + [candidate]

                            # Check cross-house (partial) constraints.
                            if not check_partial(new_assignment):
                                continue

                            # Create a new copy of the remaining sets and remove used values.
                            new_remaining = copy.deepcopy(remaining)
                            for attr in attributes:
                                new_remaining[attr].remove(candidate[attr])
                            # Recurse to next house.
                            result = search(house_index + 1, new_assignment, new_remaining)
                            if result is not None:
                                return result
    return None

def main():
    # Initialize remaining available values for each attribute.
    remaining = {
        "Name": set(NAMES),
        "HouseStyle": set(HOUSE_STYLES),
        "Mother": set(MOTHERS),
        "PhoneModel": set(PHONE_MODELS),
        "Drink": set(DRINKS),
        "Animal": set(ANIMALS)
    }

    # For fixed houses, remove the fixed values from the remaining sets right away.
    for idx, fixed in FIXED.items():
        for attr, val in fixed.items():
            if val in remaining[attr]:
                remaining[attr].remove(val)

    solution = search(0, [], remaining)
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"], "rows": []}}
    else:
        # Format the solution into the required JSON structure.
        rows = []
        # Houses are numbered 1 to 5 (we preserve order from house 0 to 4).
        for i, house in enumerate(solution):
            row = [
                str(i + 1),
                house["Name"],
                house["HouseStyle"],
                house["Mother"],
                house["PhoneModel"],
                house["Drink"],
                house["Animal"]
            ]
            rows.append(row)
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
                "rows": rows
            }
        }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()