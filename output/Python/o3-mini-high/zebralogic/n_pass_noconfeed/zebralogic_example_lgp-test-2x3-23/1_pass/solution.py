import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes for the houses.
    houses = [1, 2]  # House numbers in order from left to right
    names = ["Eric", "Arnold"]
    children = ["Bella", "Fred"]
    foods = ["grilled cheese", "pizza"]
    
    # There are 2 houses so we need to assign each attribute permutation.
    solutions = []
    for name_perm in permutations(names):
        for child_perm in permutations(children):
            for food_perm in permutations(foods):
                valid = True
                
                # Constraint 1: The person who is a pizza lover is Arnold.
                # For each house, if food is pizza then name must be Arnold.
                for i in range(len(houses)):
                    if food_perm[i] == "pizza" and name_perm[i] != "Arnold":
                        valid = False
                        break
                if not valid:
                    continue
                
                # Constraint 2: The person who loves eating grilled cheese is directly left of the person's child is named Fred.
                # This means there exists a house i (with a direct neighbor to the right, i+1)
                # such that house i has food "grilled cheese" and house i+1 has child "Fred".
                found_adjacent = False
                for i in range(len(houses) - 1):
                    if food_perm[i] == "grilled cheese" and child_perm[i+1] == "Fred":
                        found_adjacent = True
                        break
                if not found_adjacent:
                    continue
                
                # If all constraints passed, record the solution.
                solution = []
                for i in range(len(houses)):
                    # House numbers as string as required.
                    solution.append([str(houses[i]), name_perm[i], child_perm[i], food_perm[i]])
                solutions.append(solution)
    
    # We assume there is a unique solution.
    if solutions:
        return {
            "solution": {
                "header": ["House", "Name", "Children", "Food"],
                "rows": solutions[0]
            }
        }
    else:
        return {"solution": {}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))