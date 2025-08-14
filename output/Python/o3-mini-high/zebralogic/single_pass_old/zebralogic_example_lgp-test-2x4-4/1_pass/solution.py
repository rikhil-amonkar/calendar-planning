#!/usr/bin/env python3
import json
import itertools

def main():
    # Define the attributes as given in the puzzle
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]
    heights = ["very short", "short"]
    educations = ["associate", "high school"]

    solutions = []

    # Iterate over all permutations for each attribute
    for perm_names in itertools.permutations(names):
        for perm_styles in itertools.permutations(house_styles):
            # Clue 2: The person residing in a Victorian house is in the first house.
            if perm_styles[0] != "victorian":
                continue
            for perm_heights in itertools.permutations(heights):
                for perm_educations in itertools.permutations(educations):
                    # Build the houses (house 1 is index 0, house 2 is index 1)
                    houses = [
                        {
                            "House": "1",
                            "Name": perm_names[0],
                            "style": perm_styles[0],
                            "height": perm_heights[0],
                            "level of education": perm_educations[0]
                        },
                        {
                            "House": "2",
                            "Name": perm_names[1],
                            "style": perm_styles[1],
                            "height": perm_heights[1],
                            "level of education": perm_educations[1]
                        }
                    ]
                    
                    # Clue 1: The person who is short is directly left of Eric.
                    # With two houses, the only possibility is that house 1 is short and house 2 is Eric.
                    if houses[0]["height"] != "short" or houses[1]["Name"] != "Eric":
                        continue
                        
                    # Clue 3: The person who is short is the person with an associate's degree.
                    valid = True
                    for house in houses:
                        if house["height"] == "short" and house["level of education"] != "associate":
                            valid = False
                        if house["level of education"] == "associate" and house["height"] != "short":
                            valid = False
                    if not valid:
                        continue

                    # If all clues are satisfied, record the solution.
                    solutions.append(houses)

    # Assuming only one solution exists, take the first one.
    if solutions:
        solution_houses = solutions[0]
    else:
        solution_houses = []

    # Prepare the output with the required header and rows.
    output = {
        "solution": {
            "header": ["House", "Name", "style", "height", "level of education"],
            "rows": [
                [house["House"], house["Name"], house["style"], house["height"], house["level of education"]]
                for house in solution_houses
            ]
        }
    }

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()