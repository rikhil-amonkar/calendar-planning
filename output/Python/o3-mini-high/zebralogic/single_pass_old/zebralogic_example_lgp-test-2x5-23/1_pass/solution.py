#!/usr/bin/env python3
import itertools
import json

def main():
    # Define possible values for each attribute
    names = ["Arnold", "Eric"]
    level_of_education = ["associate", "high school"]
    heights = ["short", "very short"]
    lunches = ["grilled cheese", "pizza"]
    drinks = ["tea", "water"]

    solution = None

    # Iterate over all possible assignments (permutations ensure uniqueness)
    for perm_names in itertools.permutations(names):
        for perm_edu in itertools.permutations(level_of_education):
            for perm_height in itertools.permutations(heights):
                for perm_lunch in itertools.permutations(lunches):
                    for perm_drink in itertools.permutations(drinks):
                        # Construct houses for positions 1 and 2 (index 0 and 1)
                        houses = []
                        for i in range(2):
                            house = {
                                "House": str(i + 1),
                                "Name": perm_names[i],
                                "level of education": perm_edu[i],
                                "height": perm_height[i],
                                "lunch": perm_lunch[i],
                                "favorite drink": perm_drink[i]
                            }
                            houses.append(house)

                        # Clue 2: The person who loves eating grilled cheese is in the second house.
                        if houses[0]["lunch"] == "grilled cheese":
                            continue
                        if houses[1]["lunch"] != "grilled cheese":
                            continue

                        valid = True
                        for house in houses:
                            # Clue 1: The person who is very short is the person who is a pizza lover.
                            # Equivalently: house["height"] == "very short" if and only if house["lunch"] == "pizza"
                            if (house["height"] == "very short") != (house["lunch"] == "pizza"):
                                valid = False
                                break
                            # Clue 3: The person with a high school diploma is the person who is a pizza lover.
                            if (house["level of education"] == "high school") != (house["lunch"] == "pizza"):
                                valid = False
                                break
                            # Clue 4: The tea drinker is the person who loves eating grilled cheese.
                            if (house["favorite drink"] == "tea") != (house["lunch"] == "grilled cheese"):
                                valid = False
                                break
                            # Clue 5: Arnold is the person who is a pizza lover.
                            if (house["Name"] == "Arnold") != (house["lunch"] == "pizza"):
                                valid = False
                                break
                        if valid:
                            solution = houses
                            break
                    if solution:
                        break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    # Build the output JSON structure
    header = ["House", "Name", "level of education", "height", "lunch", "favorite drink"]
    rows = []
    if solution:
        for house in solution:
            row = [house[field] for field in header]
            rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()