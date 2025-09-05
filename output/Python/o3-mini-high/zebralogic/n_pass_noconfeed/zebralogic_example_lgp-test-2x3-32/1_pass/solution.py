#!/usr/bin/env python3
import json
import itertools

def solve_puzzle():
    # Define the attributes for the houses.
    houses = ["1", "2"]
    names = ["Eric", "Arnold"]
    birthdays = ["sept", "april"]
    colors = ["yellow", "red"]

    solutions = []

    # Iterate over all permutations of names, birthdays, and colors.
    for name_perm in itertools.permutations(names):
        for birthday_perm in itertools.permutations(birthdays):
            for color_perm in itertools.permutations(colors):
                # Create a candidate solution for the houses.
                assignment = []
                for i in range(len(houses)):
                    assignment.append({
                        "House": houses[i],
                        "Name": name_perm[i],
                        "Birthday": birthday_perm[i],
                        "Color": color_perm[i]
                    })
                
                # Apply constraints:

                # Clue 1: Eric is the person who loves yellow.
                # The house with color "yellow" must have Name "Eric".
                valid = True
                for house in assignment:
                    if house["Color"] == "yellow" and house["Name"] != "Eric":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 2: The person whose birthday is in April is in the first house.
                # House 1 must have birthday "april".
                if assignment[0]["Birthday"] != "april":
                    continue

                # Clue 3: The person who loves yellow is not in the first house.
                # The first house's color must not be "yellow".
                if assignment[0]["Color"] == "yellow":
                    continue

                # If all constraints are met, add the assignment to solutions.
                solutions.append(assignment)

    # Use the first found solution as the answer.
    if solutions:
        # Ensure houses are sorted by their house number.
        solution_sorted = sorted(solutions[0], key=lambda x: int(x["House"]))
        result_rows = []
        for house in solution_sorted:
            result_rows.append([house["House"], house["Name"], house["Birthday"], house["Color"]])
        output = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Color"],
                "rows": result_rows
            }
        }
    else:
        output = {"solution": None}

    # Output the solution as a JSON-formatted dictionary.
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    solve_puzzle()