import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    houses = ['1', '2']
    names = ['Eric', 'Arnold']
    lunches = ['pizza', 'grilled cheese']
    
    # Generate all possible permutations for each attribute
    name_perms = permutations(names)
    lunch_perms = permutations(lunches)
    
    # Try all possible combinations
    for name_assignment in name_perms:
        for lunch_assignment in lunch_perms:
            # Assign attributes to houses
            solution = {
                '1': {
                    'House': '1',
                    'Name': name_assignment[0],
                    'lunch': lunch_assignment[0]
                },
                '2': {
                    'House': '2',
                    'Name': name_assignment[1],
                    'lunch': lunch_assignment[1]
                }
            }
            
            # Check constraints
            # Clue 1: The person who is a pizza lover is in the second house.
            if solution['2']['lunch'] != 'pizza':
                continue
            
            # Clue 2: Arnold is not in the first house.
            if solution['1']['Name'] == 'Arnold':
                continue
            
            # If all constraints are satisfied, format the solution
            header = ['House', 'Name', 'lunch']
            rows = [
                [solution['1']['House'], solution['1']['Name'], solution['1']['lunch']],
                [solution['2']['House'], solution['2']['Name'], solution['2']['lunch']]
            ]
            
            output = {
                "solution": {
                    "header": header,
                    "rows": rows
                }
            }
            
            return json.dumps(output, indent=2)
    
    return json.dumps({"solution": {}})

if __name__ == "__main__":
    print(solve_puzzle())