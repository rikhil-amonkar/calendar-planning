import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]
    
    # House numbers
    houses = [1, 2]
    
    # Generate all possible permutations of names and house styles
    for name_perm in permutations(names):
        for style_perm in permutations(house_styles):
            # Assign to houses
            assignment = [
                {"House": str(houses[0]), "Name": name_perm[0], "house": style_perm[0]},
                {"House": str(houses[1]), "Name": name_perm[1], "house": style_perm[1]}
            ]
            
            # Check clues
            # Clue 1: Victorian is left of colonial
            clue1 = (assignment[0]["house"] == "victorian" and assignment[1]["house"] == "colonial")
            # Clue 2: Eric is in the first house
            clue2 = (assignment[0]["Name"] == "Eric")
            
            if clue1 and clue2:
                # Prepare the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "house"],
                        "rows": [
                            [str(assignment[0]["House"]), assignment[0]["Name"], assignment[0]["house"]],
                            [str(assignment[1]["House"]), assignment[1]["Name"], assignment[1]["house"]]
                        ]
                    }
                }
                return solution
    
    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the result as JSON
solution = solve_puzzle()
print(json.dumps(solution, indent=2))