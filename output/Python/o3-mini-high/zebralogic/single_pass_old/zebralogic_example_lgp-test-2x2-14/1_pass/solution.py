#!/usr/bin/env python3
import json
from itertools import permutations

def solve_puzzle():
    # Define the houses, names, and lunch options based on the puzzle rules.
    houses = [1, 2]  # House numbers: 1 and 2 (from left to right)
    names = ['Eric', 'Arnold']
    lunches = ['pizza', 'grilled cheese']

    # Try every permutation of names and lunches as assignments to houses.
    for name_assignment in permutations(names):
        for lunch_assignment in permutations(lunches):
            # Build assignments for each house (index 0 -> house 1, index 1 -> house 2)
            house1 = {"House": str(houses[0]), "Name": name_assignment[0], "lunch": lunch_assignment[0]}
            house2 = {"House": str(houses[1]), "Name": name_assignment[1], "lunch": lunch_assignment[1]}
            
            # Apply the puzzle clues:

            # Clue 1: The person who is a pizza lover is in the second house.
            if house2["lunch"] != "pizza":
                continue

            # Clue 2: Arnold is not in the first house.
            if house1["Name"] == "Arnold":
                continue

            # If all constraints are satisfied, return the solution
            return [house1, house2]
            
    return None

def main():
    solution = solve_puzzle()
    if solution is None:
        output = {
            "solution": {
                "header": ["House", "Name", "lunch"],
                "rows": []
            }
        }
    else:
        # Extract the rows in the order of houses (house 1 first, then house 2)
        rows = []
        for house in solution:
            rows.append([house["House"], house["Name"], house["lunch"]])
        output = {
            "solution": {
                "header": ["House", "Name", "lunch"],
                "rows": rows
            }
        }
    print(json.dumps(output))

if __name__ == "__main__":
    main()