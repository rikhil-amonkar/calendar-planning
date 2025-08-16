import json
from itertools import permutations

def solve_puzzle():
    # Define possible attributes
    names = ["Eric", "Arnold"]
    months = ["sept", "april"]
    colors = ["yellow", "red"]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for month_perm in permutations(months):
            for color_perm in permutations(colors):
                # Assign to houses
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Birthday", "Color"],
                        "rows": [
                            ["1", name_perm[0], month_perm[0], color_perm[0]],
                            ["2", name_perm[1], month_perm[1], color_perm[1]]
                        ]
                    }
                }
                
                # Check constraints
                rows = solution["solution"]["rows"]
                valid = True
                
                # Constraint 1: Eric loves yellow
                for row in rows:
                    if row[1] == "Eric" and row[3] != "yellow":
                        valid = False
                        break
                if not valid:
                    continue
                
                # Constraint 2: April birthday in first house
                if rows[0][2] != "april":
                    valid = False
                    continue
                
                # Constraint 3: Yellow not in first house
                if rows[0][3] == "yellow":
                    valid = False
                    continue
                
                # If all constraints passed
                if valid:
                    return solution
    
    return {"solution": {"header": [], "rows": []}}

# Solve and output
solution = solve_puzzle()
print(json.dumps(solution, indent=2))