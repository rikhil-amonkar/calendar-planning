import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ["Arnold", "Peter", "Eric", "Alice"]
    house_styles = ["victorian", "ranch", "colonial", "craftsman"]
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations
    name_perms = list(permutations(names))
    style_perms = list(permutations(house_styles))
    
    # Check all combinations
    for name_assignment in name_perms:
        for style_assignment in style_perms:
            # Create assignment dictionaries
            assignment = {}
            for i, house in enumerate(houses):
                assignment[house] = {
                    "Name": name_assignment[i],
                    "HouseStyle": style_assignment[i]
                }
            
            # Check all constraints
            # Constraint 1: Eric is in Craftsman-style house
            eric_house = None
            for house, attrs in assignment.items():
                if attrs["Name"] == "Eric":
                    eric_house = house
                    if attrs["HouseStyle"] != "craftsman":
                        break
            else:
                if eric_house is None:
                    continue
                
                # Constraint 2: Ranch directly left of Victorian
                ranch_house = None
                victorian_house = None
                for house, attrs in assignment.items():
                    if attrs["HouseStyle"] == "ranch":
                        ranch_house = house
                    if attrs["HouseStyle"] == "victorian":
                        victorian_house = house
                
                if ranch_house is None or victorian_house is None:
                    continue
                if victorian_house - ranch_house != 1:
                    continue
                
                # Constraint 3: Eric in third house
                if assignment[3]["Name"] != "Eric":
                    continue
                
                # Constraint 4: Arnold in fourth house
                if assignment[4]["Name"] != "Arnold":
                    continue
                
                # Constraint 5: Victorian house is Alice
                if assignment[victorian_house]["Name"] != "Alice":
                    continue
                
                # All constraints satisfied, return solution
                result = {
                    "solution": {
                        "header": ["House", "Name", "HouseStyle"],
                        "rows": []
                    }
                }
                
                for house in sorted(assignment.keys()):
                    attrs = assignment[house]
                    result["solution"]["rows"].append([
                        str(house),
                        attrs["Name"],
                        attrs["HouseStyle"]
                    ])
                
                return result
    
    return None

# Solve the puzzle and output the result
solution = solve_puzzle()
if solution:
    print(json.dumps(solution, indent=2))
else:
    print(json.dumps({"error": "No solution found"}, indent=2))