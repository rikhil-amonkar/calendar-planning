#!/usr/bin/env python3
import json
import itertools

# Define the attributes
houses = [1, 2]  # House numbers 1 and 2
names = ["Eric", "Arnold"]
birthdays = ["sept", "april"]
colors = ["yellow", "red"]

solutions = []

# Generate all possible assignments using permutations
for name_perm in itertools.permutations(names):
    for bday_perm in itertools.permutations(birthdays):
        for color_perm in itertools.permutations(colors):
            # Constraint 2: The person whose birthday is in April is in the first house.
            if bday_perm[0] != "april":
                continue
            # Constraint 3: The person who loves yellow is not in the first house.
            if color_perm[0] == "yellow":
                continue
            # Constraint 1: Eric is the person who loves yellow.
            valid = True
            for i in range(len(houses)):
                if name_perm[i] == "Eric" and color_perm[i] != "yellow":
                    valid = False
                    break
            if not valid:
                continue

            # If all constraints are satisfied, record the solution.
            solution_rows = []
            for idx, house in enumerate(houses):
                solution_rows.append([str(house), name_perm[idx], bday_perm[idx], color_perm[idx]])
            solutions.append(solution_rows)

# Assume there is only one unique solution, take the first one.
if solutions:
    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": solutions[0]
        }
    }
else:
    result = {"solution": {"header": ["House", "Name", "Birthday", "Color"], "rows": []}}

print(json.dumps(result, indent=2))