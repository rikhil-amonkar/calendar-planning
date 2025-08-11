import json
from itertools import permutations

def solve_puzzle():
    # Define possible attributes
    names = ["Arnold", "Peter", "Eric"]
    heights = ["short", "average", "very short"]
    houses = ["1", "2", "3"]
    
    # Generate all possible permutations for names and heights
    for name_order in permutations(names):
        for height_order in permutations(heights):
            # Assign to houses
            solution = {
                "1": {"Name": name_order[0], "height": height_order[0]},
                "2": {"Name": name_order[1], "height": height_order[1]},
                "3": {"Name": name_order[2], "height": height_order[2]},
            }
            
            # Check constraints
            # 1. Peter is somewhere to the right of Eric
            eric_house = None
            peter_house = None
            for house in ["1", "2", "3"]:
                if solution[house]["Name"] == "Eric":
                    eric_house = house
                if solution[house]["Name"] == "Peter":
                    peter_house = house
            if eric_house is None or peter_house is None or int(peter_house) <= int(eric_house):
                continue
            
            # 2. The person who is short is in the first house
            if solution["1"]["height"] != "short":
                continue
            
            # 3. One house between short and very short
            very_short_house = None
            for house in ["1", "2", "3"]:
                if solution[house]["height"] == "very short":
                    very_short_house = house
            if very_short_house is None or abs(int(very_short_house) - 1) != 2:
                continue
            
            # 4. Arnold and very short are next to each other
            arnold_house = None
            for house in ["1", "2", "3"]:
                if solution[house]["Name"] == "Arnold":
                    arnold_house = house
            if arnold_house is None or abs(int(arnold_house) - int(very_short_house)) != 1:
                continue
            
            # If all constraints are satisfied, format the solution
            formatted_solution = {
                "solution": {
                    "header": ["House", "Name", "height"],
                    "rows": [
                        ["1", solution["1"]["Name"], solution["1"]["height"]],
                        ["2", solution["2"]["Name"], solution["2"]["height"]],
                        ["3", solution["3"]["Name"], solution["3"]["height"]]
                    ]
                }
            }
            return formatted_solution
    
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))