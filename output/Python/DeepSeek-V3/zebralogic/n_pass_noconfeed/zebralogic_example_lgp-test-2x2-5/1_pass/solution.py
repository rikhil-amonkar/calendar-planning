import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]
    houses = [1, 2]
    
    # Generate all possible permutations for names and house styles
    for name_perm in permutations(names):
        for style_perm in permutations(house_styles):
            assignment = {
                1: {"Name": name_perm[0], "HouseStyle": style_perm[0]},
                2: {"Name": name_perm[1], "HouseStyle": style_perm[1]}
            }
            
            # Check clue 1: Victorian is left of colonial
            victorian_pos = None
            colonial_pos = None
            for house_num in houses:
                if assignment[house_num]["HouseStyle"] == "victorian":
                    victorian_pos = house_num
                if assignment[house_num]["HouseStyle"] == "colonial":
                    colonial_pos = house_num
            
            if victorian_pos is None or colonial_pos is None or victorian_pos >= colonial_pos:
                continue
                
            # Check clue 2: Eric is in first house
            if assignment[1]["Name"] != "Eric":
                continue
                
            # If we reach here, we found a valid solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "HouseStyle"],
                    "rows": [
                        ["1", assignment[1]["Name"], assignment[1]["HouseStyle"]],
                        ["2", assignment[2]["Name"], assignment[2]["HouseStyle"]]
                    ]
                }
            }
            return solution
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()