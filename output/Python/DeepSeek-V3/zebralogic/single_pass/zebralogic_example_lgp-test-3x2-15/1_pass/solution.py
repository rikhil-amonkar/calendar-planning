import json
from itertools import permutations

def solve_puzzle():
    # Define possible values
    names = ["Arnold", "Peter", "Eric"]
    heights = ["short", "average", "very short"]
    houses = [1, 2, 3]
    
    # Generate all possible permutations for names and heights
    for name_perm in permutations(names):
        for height_perm in permutations(heights):
            solution = {
                1: {"Name": name_perm[0], "Height": height_perm[0]},
                2: {"Name": name_perm[1], "Height": height_perm[1]},
                3: {"Name": name_perm[2], "Height": height_perm[2]}
            }
            
            # Check constraints
            # 1. Peter is somewhere to the right of Eric
            eric_pos = None
            peter_pos = None
            for house in solution:
                if solution[house]["Name"] == "Eric":
                    eric_pos = house
                if solution[house]["Name"] == "Peter":
                    peter_pos = house
            if eric_pos is None or peter_pos is None or peter_pos <= eric_pos:
                continue
            
            # 2. The person who is short is in the first house
            if solution[1]["Height"] != "short":
                continue
            
            # 3. One house between short (house 1) and very short
            very_short_pos = None
            for house in solution:
                if solution[house]["Height"] == "very short":
                    very_short_pos = house
            if very_short_pos is None or very_short_pos != 3:
                continue
            
            # 4. Arnold and very short are next to each other
            arnold_pos = None
            for house in solution:
                if solution[house]["Name"] == "Arnold":
                    arnold_pos = house
            if arnold_pos is None or abs(arnold_pos - very_short_pos) != 1:
                continue
            
            # If all constraints are satisfied, format the solution
            formatted_solution = {
                "solution": {
                    "header": ["House", "Name", "Height"],
                    "rows": [
                        ["1", solution[1]["Name"], solution[1]["Height"]],
                        ["2", solution[2]["Name"], solution[2]["Height"]],
                        ["3", solution[3]["Name"], solution[3]["Height"]]
                    ]
                }
            }
            return formatted_solution
    
    return {"solution": {"header": ["House", "Name", "Height"], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))