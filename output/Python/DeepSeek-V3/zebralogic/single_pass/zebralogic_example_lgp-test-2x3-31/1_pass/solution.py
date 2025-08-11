import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes and their possible values
    attributes = {
        "Name": ["Eric", "Arnold"],
        "favorite sport": ["basketball", "soccer"],
        "hobby": ["photography", "gardening"]
    }
    
    # Generate all possible permutations for each attribute
    name_perms = permutations(attributes["Name"])
    sport_perms = permutations(attributes["favorite sport"])
    hobby_perms = permutations(attributes["hobby"])
    
    # Iterate through all possible combinations of permutations
    for names in name_perms:
        for sports in sport_perms:
            for hobbies in hobby_perms:
                # Assign attributes to houses
                solution = {
                    1: {
                        "Name": names[0],
                        "favorite sport": sports[0],
                        "hobby": hobbies[0]
                    },
                    2: {
                        "Name": names[1],
                        "favorite sport": sports[1],
                        "hobby": hobbies[1]
                    }
                }
                
                # Check constraints
                # 1. The person who enjoys gardening is Arnold.
                gardening_arnold = True
                for house in solution:
                    if solution[house]["hobby"] == "gardening" and solution[house]["Name"] != "Arnold":
                        gardening_arnold = False
                        break
                if not gardening_arnold:
                    continue
                
                # 2. The photography enthusiast is not in the first house.
                if solution[1]["hobby"] == "photography":
                    continue
                
                # 3. The person who loves soccer is not in the first house.
                if solution[1]["favorite sport"] == "soccer":
                    continue
                
                # If all constraints are satisfied, format the solution
                result = {
                    "solution": {
                        "header": ["House", "Name", "favorite sport", "hobby"],
                        "rows": [
                            ["1", solution[1]["Name"], solution[1]["favorite sport"], solution[1]["hobby"]],
                            ["2", solution[2]["Name"], solution[2]["favorite sport"], solution[2]["hobby"]]
                        ]
                    }
                }
                return result
    
    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the result as JSON
solution = solve_puzzle()
print(json.dumps(solution, indent=2))