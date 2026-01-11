import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    names = ["Eric", "Arnold"]
    styles = ["victorian", "colonial"]
    houses = [1, 2]
    
    # Generate all possible permutations for names and styles
    name_perms = list(permutations(names, 2))
    style_perms = list(permutations(styles, 2))
    
    solutions = []
    
    # Brute-force search through all combinations
    for name_assignment in name_perms:
        for style_assignment in style_perms:
            # Create assignment dictionaries
            assignment = {}
            for i, house in enumerate(houses):
                assignment[house] = {
                    "Name": name_assignment[i],
                    "HouseStyle": style_assignment[i]
                }
            
            # Check clue 1: Victorian is to the left of colonial
            victorian_house = None
            colonial_house = None
            for house in houses:
                if assignment[house]["HouseStyle"] == "victorian":
                    victorian_house = house
                if assignment[house]["HouseStyle"] == "colonial":
                    colonial_house = house
            
            if victorian_house is None or colonial_house is None:
                continue
            
            if victorian_house >= colonial_house:
                continue
            
            # Check clue 2: Eric is in the first house
            if assignment[1]["Name"] != "Eric":
                continue
            
            # All constraints satisfied
            solutions.append(assignment)
    
    # We should have exactly one solution
    if len(solutions) != 1:
        raise ValueError(f"Expected exactly 1 solution, found {len(solutions)}")
    
    # Format the solution as required
    solution = solutions[0]
    rows = []
    for house in sorted(solution.keys()):
        row = [
            str(house),
            solution[house]["Name"],
            solution[house]["HouseStyle"]
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }
    
    return json.dumps(result, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())