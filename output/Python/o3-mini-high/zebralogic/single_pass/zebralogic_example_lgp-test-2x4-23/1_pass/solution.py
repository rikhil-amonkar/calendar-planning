#!/usr/bin/env python3
import json
from itertools import permutations

def main():
    # Define the houses and possible attributes based on the puzzle
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    mothers = ["Aniya", "Holly"]
    car_models = ["ford f150", "tesla model 3"]
    heights = ["short", "very short"]

    solutions = []

    # Iterate over all permutations for each attribute type
    for perm_names in permutations(names):
        for perm_mothers in permutations(mothers):
            for perm_cars in permutations(car_models):
                for perm_heights in permutations(heights):
                    # Construct a list of house dictionaries with their attributes
                    house_data = []
                    for i in range(len(houses)):
                        house_dict = {
                            "House": str(houses[i]),
                            "Name": perm_names[i],
                            "mothers' names": perm_mothers[i],
                            "car models": perm_cars[i],
                            "heights": perm_heights[i]
                        }
                        house_data.append(house_dict)
                    
                    # Constraint 3: The person whose mother's name is Holly is in the second house.
                    if house_data[1]["mothers' names"] != "Holly":
                        continue

                    # Constraint 2: Arnold is the person who is short.
                    valid_arnold = True
                    for house in house_data:
                        if house["Name"] == "Arnold" and house["heights"] != "short":
                            valid_arnold = False
                            break
                    if not valid_arnold:
                        continue

                    # Constraint 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
                    index_arnold = None
                    index_tesla = None
                    for idx, house in enumerate(house_data):
                        if house["Name"] == "Arnold":
                            index_arnold = idx
                        if house["car models"] == "tesla model 3":
                            index_tesla = idx
                    if index_arnold is None or index_tesla is None or index_tesla <= index_arnold:
                        continue

                    # All constraints satisfied so add this solution
                    solutions.append(house_data)

    # Assume there is a unique solution; pick the first one and sort by house number
    if solutions:
        solution = sorted(solutions[0], key=lambda x: int(x["House"]))
    else:
        solution = []

    # Prepare JSON output with required header and rows.
    header = ["House", "Name", "mothers' names", "car models", "heights"]
    rows = []
    for house in solution:
        row = [house[col] for col in header]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output))

if __name__ == '__main__':
    main()