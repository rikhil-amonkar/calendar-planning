#!/usr/bin/env python3
import json

def constraints_ok(houses, remaining_smoothies):
    # Check constraints on the current (partial) assignment.
    # houses is a list of 6 elements (each either a dict with keys "House", "Name", "Child", "Smoothie", or None)
    
    # Constraint: For each assigned house, check internal (same-house) constraints.
    for i, house in enumerate(houses):
        if house is None:
            continue
        # Clue 3: The person named "Alice" is not in the fifth house (house index 4).
        if i == 4 and house["Name"] == "Alice":
            return False
        # Clue 13: The house in the sixth position (index 5) must have Child "Meredith".
        if i == 5:
            if house["Child"] != "Meredith":
                return False
            # Clue 14: The same house must have Smoothie "dragonfruit".
            if house["Smoothie"] != "dragonfruit":
                return False
        # Clue 9: Arnold is not in the second house (index 1).
        if i == 1 and house["Name"] == "Arnold":
            return False
        # Clue 6: In the house with Name "Alice", the Child must be "Alice".
        if house["Name"] == "Alice" and house["Child"] != "Alice":
            return False
        # Also, if Child is "Alice", then Name must be "Alice".
        if house["Child"] == "Alice" and house["Name"] != "Alice":
            return False
        # Clue 7: The person who is "Alice" is also the Watermelon smoothie lover.
        if house["Name"] == "Alice" and house["Smoothie"] != "watermelon":
            return False
        if house["Smoothie"] == "watermelon" and house["Name"] != "Alice":
            return False
        # Clue 10: Bob is the mother of Timothy.
        if house["Name"] == "Bob" and house["Child"] != "Timothy":
            return False
        if house["Child"] == "Timothy" and house["Name"] != "Bob":
            return False

    # Clue 1: The house whose Child is "Fred" must be next to a house whose Smoothie is "desert".
    for i, house in enumerate(houses):
        if house is None:
            continue
        if house["Child"] == "Fred":
            neighbors = []
            if i > 0:
                neighbors.append(i - 1)
            if i < len(houses) - 1:
                neighbors.append(i + 1)
            desert_found = False
            for j in neighbors:
                if houses[j] is not None:
                    if houses[j]["Smoothie"] == "desert":
                        desert_found = True
                else:
                    # If neighbor is not assigned, check possibility.
                    if "desert" in remaining_smoothies:
                        desert_found = True
            # If all neighbors are already assigned and none is desert, it's a violation.
            if all(houses[j] is not None for j in neighbors):
                if not desert_found:
                    return False
            # Also, if a neighbor is unassigned but desert is not available, then violation.
            if any(houses[j] is None for j in neighbors):
                if "desert" not in remaining_smoothies and not desert_found:
                    return False

    # Clue 2: The house with Blueberry smoothie must be somewhere to the left of the house with Child "Fred".
    index_blueberry = None
    index_fred = None
    for i, house in enumerate(houses):
        if house is None:
            continue
        if house["Smoothie"] == "blueberry":
            index_blueberry = i
        if house["Child"] == "Fred":
            index_fred = i
    if index_blueberry is not None and index_fred is not None:
        if index_blueberry >= index_fred:
            return False

    # Clue 5: The Watermelon smoothie lover (i.e. Alice) is somewhere to the right of the house that likes Cherry.
    index_cherry = None
    index_watermelon = None
    for i, house in enumerate(houses):
        if house is None:
            continue
        if house["Smoothie"] == "cherry":
            index_cherry = i
        if house["Smoothie"] == "watermelon":
            index_watermelon = i
    if index_cherry is not None and index_watermelon is not None:
        if index_cherry >= index_watermelon:
            return False

    # Clue 8: The house whose Child is "Samantha" is to the left of the house with Name "Peter".
    index_samantha = None
    index_peter = None
    for i, house in enumerate(houses):
        if house is None:
            continue
        if house["Child"] == "Samantha":
            index_samantha = i
        if house["Name"] == "Peter":
            index_peter = i
    if index_samantha is not None and index_peter is not None:
        if index_samantha >= index_peter:
            return False

    # Clue 11: Arnold is directly left of Carol.
    # Check any adjacent pair where if a house is Arnold, the next must be Carol.
    for i in range(len(houses) - 1):
        if houses[i] is not None and houses[i + 1] is not None:
            if houses[i]["Name"] == "Arnold" and houses[i + 1]["Name"] != "Carol":
                return False
    # Also, if a house is Carol and its left neighbor is assigned, it must be Arnold.
    for i in range(len(houses)):
        if houses[i] is not None and houses[i]["Name"] == "Carol":
            if i == 0:
                return False
            if houses[i - 1] is not None and houses[i - 1]["Name"] != "Arnold":
                return False
    # If both Arnold and Carol are assigned, ensure they are consecutive.
    index_arnold = None
    index_carol = None
    for i, house in enumerate(houses):
        if house is None:
            continue
        if house["Name"] == "Arnold":
            index_arnold = i
        if house["Name"] == "Carol":
            index_carol = i
    if index_arnold is not None and index_carol is not None:
        if index_carol - index_arnold != 1:
            return False

    # Clue 12: The house with Cherry smoothie is directly left of the house whose Child is "Samantha".
    # Check adjacent houses.
    for i in range(len(houses) - 1):
        if houses[i] is not None and houses[i + 1] is not None:
            if houses[i]["Smoothie"] == "cherry" and houses[i + 1]["Child"] != "Samantha":
                return False
            if houses[i + 1]["Child"] == "Samantha" and houses[i]["Smoothie"] != "cherry":
                return False
    # Also, if both are assigned anywhere, they must be adjacent.
    idx_cherry = None
    idx_samantha = None
    for i, house in enumerate(houses):
        if house is None:
            continue
        if house["Smoothie"] == "cherry":
            idx_cherry = i
        if house["Child"] == "Samantha":
            idx_samantha = i
    if idx_cherry is not None and idx_samantha is not None:
        if idx_samantha - idx_cherry != 1:
            return False

    return True

def backtrack(houses, house_index, remaining_names, remaining_children, remaining_smoothies, solutions):
    if house_index == 6:
        if constraints_ok(houses, remaining_smoothies):
            solutions.append([house.copy() for house in houses])
        return

    for name in list(remaining_names):
        for child in list(remaining_children):
            for smoothie in list(remaining_smoothies):
                # Enforce same-house pairings based on clues.
                # Clue 6 & 7: If Name is "Alice", then Child must be "Alice" and Smoothie must be "watermelon".
                if name == "Alice":
                    if child != "Alice" or smoothie != "watermelon":
                        continue
                if child == "Alice" and name != "Alice":
                    continue
                # Clue 10: Bob must have Timothy.
                if name == "Bob":
                    if child != "Timothy":
                        continue
                if child == "Timothy" and name != "Bob":
                    continue
                # Clues 13 & 14: In the sixth house (index 5) Child must be "Meredith" and Smoothie "dragonfruit".
                if house_index == 5:
                    if child != "Meredith" or smoothie != "dragonfruit":
                        continue
                # Clue 3: "Alice" is not in the fifth house.
                if house_index == 4 and name == "Alice":
                    continue
                # Clue 9: Arnold is not in the second house.
                if house_index == 1 and name == "Arnold":
                    continue

                houses[house_index] = {
                    "House": str(house_index + 1),
                    "Name": name,
                    "Child": child,
                    "Smoothie": smoothie
                }
                new_remaining_names = remaining_names - {name}
                new_remaining_children = remaining_children - {child}
                new_remaining_smoothies = remaining_smoothies - {smoothie}

                if constraints_ok(houses, new_remaining_smoothies):
                    backtrack(houses, house_index + 1, new_remaining_names, new_remaining_children, new_remaining_smoothies, solutions)
                houses[house_index] = None

def main():
    names = {"Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"}
    children = {"Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"}
    smoothies = {"desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"}
    
    houses = [None] * 6
    solutions = []
    backtrack(houses, 0, names, children, smoothies, solutions)
    
    if solutions:
        solution = solutions[0]
        header = ["House", "Name", "child", "smoothie"]
        rows = []
        for house in solution:
            rows.append([house["House"], house["Name"], house["Child"], house["Smoothie"]])
        output = {"solution": {"header": header, "rows": rows}}
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": {}}))

if __name__ == '__main__':
    main()