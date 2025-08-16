#!/usr/bin/env python3
import itertools
import json

def solve_zebra_puzzle():
    names = ["Eric", "Arnold"]
    houseStyles = ["victorian", "colonial"]
    heights = ["very short", "short"]
    educations = ["associate", "high school"]

    solution = None

    for name_perm in itertools.permutations(names):
        for style_perm in itertools.permutations(houseStyles):
            for height_perm in itertools.permutations(heights):
                for edu_perm in itertools.permutations(educations):
                    houses = []
                    for i in range(2):
                        house = {
                            "House": str(i+1),
                            "Name": name_perm[i],
                            "HouseStyle": style_perm[i],
                            "Height": height_perm[i],
                            "Education": edu_perm[i]
                        }
                        houses.append(house)
                    # Constraint 2: The Victorian house is in the first house.
                    if houses[0]["HouseStyle"] != "victorian":
                        continue
                    # Constraint 1: The person who is short is directly left of Eric.
                    # Find the position of Eric.
                    eric_index = None
                    for idx, house in enumerate(houses):
                        if house["Name"] == "Eric":
                            eric_index = idx
                            break
                    if eric_index is None or eric_index == 0:
                        continue
                    if houses[eric_index - 1]["Height"] != "short":
                        continue
                    # Constraint 3: The person who is short is the person with an associate's degree.
                    valid = True
                    for house in houses:
                        if house["Height"] == "short" and house["Education"] != "associate":
                            valid = False
                        if house["Education"] == "associate" and house["Height"] != "short":
                            valid = False
                    if not valid:
                        continue
                    solution = houses
                    break
                if solution:
                    break
            if solution:
                break
        if solution:
            break
    return solution

def main():
    solution = solve_zebra_puzzle()
    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Height", "Education"],
            "rows": [
                [house["House"], house["Name"], house["HouseStyle"], house["Height"], house["Education"]]
                for house in sorted(solution, key=lambda x: int(x["House"]))
            ] if solution else []
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()