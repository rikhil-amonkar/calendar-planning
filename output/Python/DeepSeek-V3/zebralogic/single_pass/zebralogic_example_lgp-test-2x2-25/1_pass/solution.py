import json
from itertools import permutations

def solve_puzzle():
    # Define the possible attributes
    names = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]
    
    # Generate all possible permutations for names and vacations
    for name_order in permutations(names):
        for vacation_order in permutations(vacations):
            # Create the house assignments
            solution = {
                1: {"Name": name_order[0], "Vacation": vacation_order[0]},
                2: {"Name": name_order[1], "Vacation": vacation_order[1]}
            }
            
            # Check the clues
            # Clue 1: Arnold is to the right of the person who loves beach vacations
            beach_house = None
            arnold_house = None
            for house in [1, 2]:
                if solution[house]["Vacation"] == "beach":
                    beach_house = house
                if solution[house]["Name"] == "Arnold":
                    arnold_house = house
            if beach_house is not None and arnold_house is not None:
                if arnold_house > beach_house:
                    # Format the solution
                    result = {
                        "solution": {
                            "header": ["House", "Name", "Vacation"],
                            "rows": [
                                ["1", solution[1]["Name"], solution[1]["Vacation"]],
                                ["2", solution[2]["Name"], solution[2]["Vacation"]]
                            ]
                        }
                    }
                    return json.dumps(result, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())