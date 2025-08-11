import json
from itertools import permutations

def solve_puzzle():
    # Define all possible attributes
    names = ["Eric", "Arnold"]
    mothers = ["Aniya", "Holly"]
    cars = ["ford f150", "tesla model 3"]
    heights = ["short", "very short"]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for car_perm in permutations(cars):
                for height_perm in permutations(heights):
                    # Check all constraints
                    # Constraint 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
                    if car_perm[0] == "tesla model 3":
                        continue  # Tesla is to the left of Arnold, which violates the constraint
                    
                    # Constraint 2: Arnold is the person who is short.
                    if name_perm[0] == "Arnold" and height_perm[0] != "short":
                        continue
                    if name_perm[1] == "Arnold" and height_perm[1] != "short":
                        continue
                    
                    # Constraint 3: The person whose mother's name is Holly is in the second house.
                    if mother_perm[1] != "Holly":
                        continue
                    
                    # If all constraints are satisfied, construct the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Car", "Height"],
                            "rows": [
                                ["1", name_perm[0], mother_perm[0], car_perm[0], height_perm[0]],
                                ["2", name_perm[1], mother_perm[1], car_perm[1], height_perm[1]]
                            ]
                        }
                    }
                    return solution
    
    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the JSON output
solution = solve_puzzle()
print(json.dumps(solution, indent=2))