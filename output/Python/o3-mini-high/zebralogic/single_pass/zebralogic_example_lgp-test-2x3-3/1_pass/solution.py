#!/usr/bin/env python3
import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes for each category
    names = ["Arnold", "Eric"]
    foods = ["grilled cheese", "pizza"]
    mothers = ["Holly", "Aniya"]
    
    # There are 2 houses: index 0 represents House 1 (left) and index 1 represents House 2 (right)
    solution = None
    
    # Iterate over all possible assignments (permutations) for each attribute
    for name_perm in permutations(names):
        for food_perm in permutations(foods):
            for mother_perm in permutations(mothers):
                # Constraint 1: The person who loves grilled cheese is directly left of the person who is a pizza lover.
                # Since there are only 2 houses, the only possibility is:
                # House 1 must have grilled cheese and House 2 must have pizza.
                if not (food_perm[0] == "grilled cheese" and food_perm[1] == "pizza"):
                    continue
                
                # Constraint 2: Arnold is not in the second house.
                if name_perm[1] == "Arnold":
                    continue
                
                # Constraint 3: Arnold's mother is Holly.
                valid = True
                for i in range(2):
                    if name_perm[i] == "Arnold" and mother_perm[i] != "Holly":
                        valid = False
                        break
                if not valid:
                    continue
                
                # If all constraints are satisfied, record this solution.
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Food", "Mother"],
                        "rows": [
                            ["1", name_perm[0], food_perm[0], mother_perm[0]],
                            ["2", name_perm[1], food_perm[1], mother_perm[1]]
                        ]
                    }
                }
                return solution
    return solution

if __name__ == "__main__":
    sol = solve_puzzle()
    if sol:
        print(json.dumps(sol, indent=2))
    else:
        print(json.dumps({"solution": {"header": ["House", "Name", "Food", "Mother"], "rows": []}}, indent=2))