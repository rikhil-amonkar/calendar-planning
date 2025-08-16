import json
from itertools import permutations

def solve_puzzle():
    # Define possible values for each attribute
    names = ["Eric", "Arnold"]
    mothers = ["Aniya", "Holly"]
    car_models = ["ford f150", "tesla model 3"]
    heights = ["short", "very short"]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for car_perm in permutations(car_models):
                for height_perm in permutations(heights):
                    # Check all constraints
                    # Constraint 1: Tesla is to the right of Arnold
                    arnold_pos = name_perm.index("Arnold") + 1
                    tesla_pos = car_perm.index("tesla model 3") + 1
                    if tesla_pos <= arnold_pos:
                        continue
                    
                    # Constraint 2: Arnold is short
                    if height_perm[name_perm.index("Arnold")] != "short":
                        continue
                    
                    # Constraint 3: Mother Holly is in house 2
                    if mother_perm[1] != "Holly":
                        continue
                    
                    # If all constraints are satisfied, construct the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "CarModel", "Height"],
                            "rows": [
                                ["1", name_perm[0], mother_perm[0], car_perm[0], height_perm[0]],
                                ["2", name_perm[1], mother_perm[1], car_perm[1], height_perm[1]]
                            ]
                        }
                    }
                    return solution
    
    return {"solution": {"header": [], "rows": []}}

# Solve and output the puzzle
solution = solve_puzzle()
print(json.dumps(solution, indent=2))