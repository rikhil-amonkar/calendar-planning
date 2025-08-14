#!/usr/bin/env python3
import itertools
import json

def main():
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    birthday_months = ["april", "sept"]
    mothers = ["Aniya", "Holly"]

    solution = None

    # Iterate through all possible assignments.
    for name_perm in itertools.permutations(names):
        for month_perm in itertools.permutations(birthday_months):
            # Clue 2: The person whose birthday is in April is in the first house.
            if month_perm[0] != "april":
                continue
            for mother_perm in itertools.permutations(mothers):
                # Build the house assignments for each house.
                assignment = [
                    {"House": str(house), "Name": name, "birthday month": month, "mother's name": mother}
                    for house, name, month, mother in zip(houses, name_perm, month_perm, mother_perm)
                ]
                # Clue 1: Eric is somewhere to the left of the person whose mother's name is Holly.
                eric_index = next(i for i, h in enumerate(assignment) if h["Name"] == "Eric")
                holly_index = next(i for i, h in enumerate(assignment) if h["mother's name"] == "Holly")
                if eric_index < holly_index:
                    solution = assignment
                    break
            if solution:
                break
        if solution:
            break

    # Prepare the output in the required JSON format.
    output = {
        "solution": {
            "header": ["House", "Name", "birthday month", "mother's name"],
            "rows": [
                [house["House"], house["Name"], house["birthday month"], house["mother's name"]]
                for house in solution
            ]
        }
    }
    print(json.dumps(output))

if __name__ == '__main__':
    main()