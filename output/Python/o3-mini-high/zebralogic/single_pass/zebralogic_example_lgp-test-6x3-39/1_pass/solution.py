#!/usr/bin/env python3
import json

# Define the domains for each attribute
NAMES = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
CHILDREN = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
SMOOTHIES = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]

def validate_global(solution):
    # solution is a list of 6 dicts, with keys: "Name", "Children", "Smoothie"
    # Index: 0 -> House 1, ..., 5 -> House 6
    
    # Clue 9: Arnold is not in the second house.
    if solution[1]["Name"] == "Arnold":
        return False
    # Clue 3: Alice is not in the fifth house.
    if solution[4]["Name"] == "Alice":
        return False
    # Clue 4: The person whose child is Samantha is not in the second house.
    if solution[1]["Children"] == "Samantha":
        return False
    # Clue 13 & 14: House 6 must have child Meredith and smoothie dragonfruit.
    if solution[5]["Children"] != "Meredith" or solution[5]["Smoothie"] != "dragonfruit":
        return False

    # Forced associations for names:
    # Clue 6 & 7: If Name is Alice then child must be Alice and smoothie must be watermelon.
    for house in solution:
        if house["Name"] == "Alice":
            if house["Children"] != "Alice" or house["Smoothie"] != "watermelon":
                return False
        if house["Name"] == "Bob":
            # Clue 10: Bob is the mother of Timothy.
            if house["Children"] != "Timothy":
                return False

    # Clue 11: Arnold is directly left of Carol.
    for i in range(6):
        if solution[i]["Name"] == "Arnold":
            if i == 5 or solution[i+1]["Name"] != "Carol":
                return False
        if solution[i]["Name"] == "Carol":
            if i == 0 or solution[i-1]["Name"] != "Arnold":
                return False

    # Clue 12: The person who likes Cherry smoothies is directly left of the person whose child is Samantha.
    for i in range(6):
        if solution[i]["Smoothie"] == "cherry":
            if i == 5 or solution[i+1]["Children"] != "Samantha":
                return False
    for i in range(6):
        if solution[i]["Children"] == "Samantha":
            if i == 0 or solution[i-1]["Smoothie"] != "cherry":
                return False

    # Clue 2: The person who drinks Blueberry smoothies is somewhere to the left of the person whose child is Fred.
    blueberry_index = None
    fred_index = None
    for i in range(6):
        if solution[i]["Smoothie"] == "blueberry":
            blueberry_index = i
        if solution[i]["Children"] == "Fred":
            fred_index = i
    if blueberry_index is None or fred_index is None or blueberry_index >= fred_index:
        return False

    # Clue 5: The Watermelon smoothie lover is somewhere to the right of the person who likes Cherry smoothies.
    cherry_index = None
    watermelon_index = None
    for i in range(6):
        if solution[i]["Smoothie"] == "cherry":
            cherry_index = i
        if solution[i]["Smoothie"] == "watermelon":
            watermelon_index = i
    # There must be a cherry somewhere and watermelon (which will be in Alice's house)
    if cherry_index is None or watermelon_index is None or cherry_index >= watermelon_index:
        return False

    # Clue 8: Peter is somewhere to the right of the person whose child is Samantha.
    peter_index = None
    samantha_child_index = None
    for i in range(6):
        if solution[i]["Name"] == "Peter":
            peter_index = i
        if solution[i]["Children"] == "Samantha":
            samantha_child_index = i
    if peter_index is None or samantha_child_index is None or samantha_child_index >= peter_index:
        return False

    # Clue 1: The house with child Fred must be next door to the house with the desert smoothie.
    for i in range(6):
        if solution[i]["Children"] == "Fred":
            if i == 0:
                if solution[1]["Smoothie"] != "desert":
                    return False
            elif i == 5:
                if solution[4]["Smoothie"] != "desert":
                    return False
            else:
                if solution[i-1]["Smoothie"] != "desert" and solution[i+1]["Smoothie"] != "desert":
                    return False

    return True

def search(house_index, current_solution, rem_names, rem_children, rem_smoothies):
    # If all houses assigned, check global constraints.
    if house_index == 6:
        if validate_global(current_solution):
            return current_solution
        else:
            return None

    # Prepare candidate options based on neighbor constraints and house-index specific rules.
    candidates = []
    
    # If the previous house's name was Arnold then current must be Carol.
    if house_index > 0 and current_solution[house_index-1]["Name"] == "Arnold":
        name_options = ["Carol"] if "Carol" in rem_names else []
    else:
        name_options = list(rem_names)
    # House-specific restrictions:
    # Clue 9: House 2 (index 1) cannot be Arnold.
    if house_index == 1 and "Arnold" in name_options:
        name_options.remove("Arnold")
    # Clue 3: House 5 (index 4) cannot be Alice.
    if house_index == 4 and "Alice" in name_options:
        name_options.remove("Alice")
    # For House 6 (index 5), the child and smoothie are forced, and Alice or Bob would conflict.
    if house_index == 5:
        if "Alice" in name_options:
            name_options.remove("Alice")
        if "Bob" in name_options:
            name_options.remove("Bob")
    
    # For each candidate name, decide on forced child options.
    for name in name_options:
        # Determine candidate child options
        # If left neighbor's smoothie is cherry, current child must be Samantha.
        if house_index > 0 and current_solution[house_index-1]["Smoothie"] == "cherry":
            child_options = ["Samantha"] if "Samantha" in rem_children else []
        else:
            child_options = list(rem_children)
        # Forced pairing: if name is "Alice", then child must be "Alice" and smoothie must be "watermelon"
        if name == "Alice":
            if "Alice" not in child_options:
                continue
            child_options = ["Alice"]
        # Forced pairing: if name is "Bob", then child must be "Timothy"
        if name == "Bob":
            if "Timothy" not in child_options:
                continue
            child_options = ["Timothy"]
        # For House 6 (index 5), child is forced to be Meredith.
        if house_index == 5:
            if "Meredith" not in child_options:
                continue
            child_options = ["Meredith"]
            
        # Determine candidate smoothie options
        # For House 6 (index 5), smoothie is forced to be dragonfruit.
        if house_index == 5:
            smoothie_options = ["dragonfruit"] if "dragonfruit" in rem_smoothies else []
        else:
            # If name is "Alice", smoothie must be watermelon.
            if name == "Alice":
                if "watermelon" not in rem_smoothies:
                    continue
                smoothie_options = ["watermelon"]
            else:
                smoothie_options = list(rem_smoothies)
            # If this is the first house, watermelon is not allowed because of ordering (watermelon must be to right of cherry)
            if house_index == 0 and "watermelon" in smoothie_options:
                smoothie_options.remove("watermelon")
        
        # Now iterate over combinations of child and smoothie options.
        for child in child_options:
            # Additional neighbor check:
            # If this house's child is Samantha, then the left neighbor's smoothie must be cherry.
            if child == "Samantha" and house_index > 0:
                if current_solution[house_index-1]["Smoothie"] != "cherry":
                    continue
            # Also, if left neighbor's smoothie is cherry, then current child must be Samantha.
            if house_index > 0 and current_solution[house_index-1]["Smoothie"] == "cherry" and child != "Samantha":
                continue
            # Also, house 0 cannot have child Fred because clue 2 (blueberry must be to left of Fred).
            if house_index == 0 and child == "Fred":
                continue

            for smoothie in smoothie_options:
                # If current candidate child is Samantha but left neighbor is not cherry, skip (already checked above).
                # If name is Carol, then left neighbor must be Arnold.
                if name == "Carol":
                    if house_index == 0 or current_solution[house_index-1]["Name"] != "Arnold":
                        continue
                # Also, if current candidate's name is not Carol but left neighbor is Arnold, we already restricted name_options.
                # If candidate smoothie is watermelon in house 0 (shouldn't happen because already removed for non-Alice)
                if house_index == 0 and smoothie == "watermelon":
                    continue

                # Form the candidate triple for the current house.
                candidate = {"Name": name, "Children": child, "Smoothie": smoothie}

                # Create new remaining sets for next recursion step
                new_rem_names = rem_names.copy()
                new_rem_children = rem_children.copy()
                new_rem_smoothies = rem_smoothies.copy()
                new_rem_names.remove(name)
                new_rem_children.remove(child)
                new_rem_smoothies.remove(smoothie)

                next_solution = current_solution + [candidate]
                result = search(house_index + 1, next_solution, new_rem_names, new_rem_children, new_rem_smoothies)
                if result is not None:
                    return result
    return None

def solve_puzzle():
    # Start with all available elements in each category.
    rem_names = set(NAMES)
    rem_children = set(CHILDREN)
    rem_smoothies = set(SMOOTHIES)
    solution = search(0, [], rem_names, rem_children, rem_smoothies)
    return solution

def main():
    solution = solve_puzzle()
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "Children", "Smoothie"], "rows": []}}
    else:
        rows = []
        for i, house in enumerate(solution):
            # House numbers are 1-indexed
            rows.append([str(i+1), house["Name"], house["Children"], house["Smoothie"]])
        output = {"solution": {"header": ["House", "Name", "Children", "Smoothie"], "rows": rows}}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()