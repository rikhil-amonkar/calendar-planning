#!/usr/bin/env python3
import json

# This function checks the constraints on the current (partial or complete) assignment.
# The assignment is a list of 5 elements (one per house, index 0 is house 1, etc).
# Each element is either None or a dictionary with keys: "House", "Name", "Height", "Mother", "HairColor".
def valid_assignment(assignment, complete=False):
    # Check individual house constraints.
    for i, house in enumerate(assignment):
        if house is None:
            continue
        # Constraint 1: The person who is tall is the person whose mother's name is Holly.
        if house.get("Height") == "tall" and house.get("Mother") is not None and house["Mother"] != "Holly":
            return False
        if house.get("Mother") == "Holly" and house.get("Height") is not None and house["Height"] != "tall":
            return False

        # Constraint 6: The person who is very short is the person whose mother's name is Penny.
        if house.get("Height") == "very short" and house.get("Mother") is not None and house["Mother"] != "Penny":
            return False
        if house.get("Mother") == "Penny" and house.get("Height") is not None and house["Height"] != "very short":
            return False

        # Constraint 5: Eric is the person who has black hair.
        if house.get("Name") == "Eric" and house.get("HairColor") is not None and house["HairColor"] != "black":
            return False
        if house.get("HairColor") == "black" and house.get("Name") is not None and house["Name"] != "Eric":
            return False

        # Constraint 9: The person who has red hair is Peter.
        if house.get("HairColor") == "red" and house.get("Name") is not None and house["Name"] != "Peter":
            return False
        if house.get("Name") == "Peter" and house.get("HairColor") is not None and house["HairColor"] != "red":
            return False

        # Constraint 11: Arnold is the person who has brown hair.
        if house.get("Name") == "Arnold" and house.get("HairColor") is not None and house["HairColor"] != "brown":
            return False
        if house.get("HairColor") == "brown" and house.get("Name") is not None and house["Name"] != "Arnold":
            return False

        # Constraint 14: The person whose mother's name is Kailyn is in the third house.
        # (House 3 is index 2.)
        if i == 2 and house.get("Mother") is not None and house["Mother"] != "Kailyn":
            return False

        # Constraint 8: Bob is in the fifth house.
        if i == 4 and house.get("Name") is not None and house["Name"] != "Bob":
            return False

    # Constraint 10: The person whose mother's name is Kailyn is directly left of the person who is short.
    # Check only on adjacent houses that are both assigned.
    for i in range(4):
        if assignment[i] is not None and assignment[i+1] is not None:
            if assignment[i].get("Mother") == "Kailyn" and assignment[i+1].get("Height") is not None and assignment[i+1]["Height"] != "short":
                return False
            if assignment[i+1].get("Height") == "short" and assignment[i].get("Mother") is not None and assignment[i]["Mother"] != "Kailyn":
                return False

    # Constraint 2: There are two houses between the person who has an average height and the person who is short.
    avg_index = None
    short_index = None
    for i, house in enumerate(assignment):
        if house is not None and house.get("Height") == "average":
            avg_index = i
        if house is not None and house.get("Height") == "short":
            short_index = i
    if avg_index is not None and short_index is not None:
        if abs(avg_index - short_index) != 3:
            return False

    # Constraint 3: The person who has gray hair is directly left of the person whose mother's name is Janelle.
    index_gray = None
    index_janelle = None
    for i, house in enumerate(assignment):
        if house is not None and house.get("HairColor") == "gray":
            index_gray = i
        if house is not None and house.get("Mother") == "Janelle":
            index_janelle = i
    if index_gray is not None and index_janelle is not None:
        if index_gray + 1 != index_janelle:
            return False

    # Constraint 7: Eric and the person who has gray hair are next to each other.
    index_eric = None
    if index_gray is not None:
        for i, house in enumerate(assignment):
            if house is not None and house.get("Name") == "Eric":
                index_eric = i
        if index_eric is not None:
            if abs(index_eric - index_gray) != 1:
                return False

    # Constraint 12: The person who has brown hair is somewhere to the left of the person whose mother's name is Janelle.
    index_brown = None
    for i, house in enumerate(assignment):
        if house is not None and house.get("HairColor") == "brown":
            index_brown = i
    if index_brown is not None and index_janelle is not None:
        if index_brown >= index_janelle:
            return False

    # Constraint 13: The person whose mother's name is Aniya and the person who is very short are next to each other.
    index_aniya = None
    index_veryshort = None
    for i, house in enumerate(assignment):
        if house is not None and house.get("Mother") == "Aniya":
            index_aniya = i
        if house is not None and house.get("Height") == "very short":
            index_veryshort = i
    if index_aniya is not None and index_veryshort is not None:
        if abs(index_aniya - index_veryshort) != 1:
            return False

    # For complete assignments, no extra check is needed since uniqueness is ensured by the backtracking.
    return True

# Backtracking search: assign houses 1-5 one by one.
def backtrack(i, assignment, names, heights, mothers, hairs):
    if i == 5:
        # Assignment complete; check full constraints.
        if valid_assignment(assignment, complete=True):
            return assignment
        else:
            return None

    # Loop over available assignments for the i-th house.
    for name in list(names):
        # Constraint 8: Bob is in the fifth house.
        if i == 4 and name != "Bob":
            continue
        for height in list(heights):
            for mother in list(mothers):
                # Constraint 14: House 3 (index 2) must have mother's Kailyn.
                if i == 2 and mother != "Kailyn":
                    continue
                for hair in list(hairs):
                    # Constraint 4: The person who has black hair is not in the fourth house.
                    if i == 3 and hair == "black":
                        continue

                    # Enforce direct name-hair relationships:
                    # Constraint 5 and its converse: Eric <-> black.
                    if name == "Eric" and hair != "black":
                        continue
                    if hair == "black" and name != "Eric":
                        continue
                    # Constraint 9 and its converse: Peter <-> red.
                    if name == "Peter" and hair != "red":
                        continue
                    if hair == "red" and name != "Peter":
                        continue
                    # Constraint 11 and its converse: Arnold <-> brown.
                    if name == "Arnold" and hair != "brown":
                        continue
                    if hair == "brown" and name != "Arnold":
                        continue

                    # Enforce house-specific height-mother links:
                    # Constraint 1: tall <-> Holly.
                    if height == "tall" and mother != "Holly":
                        continue
                    if mother == "Holly" and height != "tall":
                        continue
                    # Constraint 6: very short <-> Penny.
                    if height == "very short" and mother != "Penny":
                        continue
                    if mother == "Penny" and height != "very short":
                        continue

                    # Enforce immediate neighbor rule for constraint 10 if previous house is assigned.
                    if i > 0 and assignment[i-1] is not None:
                        # If the previous house has mother's Kailyn, then current house must be short.
                        if assignment[i-1].get("Mother") == "Kailyn" and height != "short":
                            continue
                        # Conversely, if current house is short and previous house is assigned a mother, it must be Kailyn.
                        if height == "short" and assignment[i-1].get("Mother") is not None and assignment[i-1]["Mother"] != "Kailyn":
                            continue

                    # Prepare the candidate assignment for the current house.
                    house_assignment = {
                        "House": str(i+1),
                        "Name": name,
                        "Height": height,
                        "Mother": mother,
                        "HairColor": hair
                    }
                    assignment[i] = house_assignment

                    if not valid_assignment(assignment, complete=False):
                        assignment[i] = None
                        continue

                    # Update available attribute sets.
                    new_names = names - {name}
                    new_heights = heights - {height}
                    new_mothers = mothers - {mother}
                    new_hairs = hairs - {hair}

                    result = backtrack(i+1, assignment, new_names, new_heights, new_mothers, new_hairs)
                    if result is not None:
                        return result
                    assignment[i] = None
    return None

def main():
    # Define the sets for the attributes.
    names = {"Alice", "Peter", "Bob", "Eric", "Arnold"}
    heights = {"very short", "short", "tall", "average", "very tall"}
    mothers = {"Janelle", "Kailyn", "Penny", "Holly", "Aniya"}
    hairs = {"blonde", "black", "gray", "red", "brown"}

    # Prepare a list for 5 houses (indexes 0..4).
    assignment = [None] * 5

    solution = backtrack(0, assignment, names, heights, mothers, hairs)
    
    if solution is None:
        output = {
            "solution": {
                "header": ["House", "Name", "Height", "Mother", "HairColor"],
                "rows": []
            }
        }
    else:
        rows = []
        for house in solution:
            rows.append([house["House"], house["Name"], house["Height"], house["Mother"], house["HairColor"]])
        output = {
            "solution": {
                "header": ["House", "Name", "Height", "Mother", "HairColor"],
                "rows": rows
            }
        }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()