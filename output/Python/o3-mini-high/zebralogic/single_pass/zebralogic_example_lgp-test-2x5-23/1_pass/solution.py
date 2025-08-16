#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    # Define the possible attribute values for each category.
    names = ["Arnold", "Eric"]
    educations = ["associate", "high school"]
    heights = ["short", "very short"]
    foods = ["grilled cheese", "pizza"]
    drinks = ["tea", "water"]

    # Iterate over all permutations of attributes for the houses.
    for names_perm in itertools.permutations(names):
        for educations_perm in itertools.permutations(educations):
            for heights_perm in itertools.permutations(heights):
                for foods_perm in itertools.permutations(foods):
                    # Clue 2: The person who loves grilled cheese is in the second house.
                    if foods_perm[1] != "grilled cheese":
                        continue
                    for drinks_perm in itertools.permutations(drinks):
                        valid = True
                        for i in range(2):
                            # Clue 1: The person who is very short is the person who is a pizza lover.
                            if heights_perm[i] == "very short" and foods_perm[i] != "pizza":
                                valid = False
                                break
                            # Clue 3: The person with a high school diploma is the person who is a pizza lover.
                            if educations_perm[i] == "high school" and foods_perm[i] != "pizza":
                                valid = False
                                break
                            # Clue 4: The tea drinker is the person who loves eating grilled cheese.
                            if drinks_perm[i] == "tea" and foods_perm[i] != "grilled cheese":
                                valid = False
                                break
                            # Clue 5: Arnold is the person who is a pizza lover.
                            if names_perm[i] == "Arnold" and foods_perm[i] != "pizza":
                                valid = False
                                break
                            # Enforce bidirectional relationships:
                            if foods_perm[i] == "pizza":
                                if not (heights_perm[i] == "very short" and educations_perm[i] == "high school" and names_perm[i] == "Arnold"):
                                    valid = False
                                    break
                            if foods_perm[i] == "grilled cheese" and drinks_perm[i] != "tea":
                                valid = False
                                break
                        if valid:
                            # Build the solution in the required JSON structure.
                            solution_rows = []
                            for idx in range(2):
                                house_number = str(idx + 1)
                                solution_rows.append([
                                    house_number,
                                    names_perm[idx],
                                    educations_perm[idx],
                                    heights_perm[idx],
                                    foods_perm[idx],
                                    drinks_perm[idx]
                                ])
                            return {
                                "solution": {
                                    "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
                                    "rows": solution_rows
                                }
                            }
    return None

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result))