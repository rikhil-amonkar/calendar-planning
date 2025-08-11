import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    houses = [1, 2]
    names = ['Arnold', 'Eric']
    months = ['april', 'sept']
    mothers = ['Aniya', 'Holly']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for month_perm in permutations(months):
            for mother_perm in permutations(mothers):
                # Assign attributes to houses
                assignment = [
                    {
                        'House': '1',
                        'Name': name_perm[0],
                        'birthday month': month_perm[0],
                        "mother's name": mother_perm[0]
                    },
                    {
                        'House': '2',
                        'Name': name_perm[1],
                        'birthday month': month_perm[1],
                        "mother's name": mother_perm[1]
                    }
                ]
                
                # Check constraints
                # Constraint 1: Eric is to the left of the person whose mother's name is Holly
                eric_house = None
                holly_house = None
                for house in assignment:
                    if house['Name'] == 'Eric':
                        eric_house = house['House']
                    if house["mother's name"] == 'Holly':
                        holly_house = house['House']
                if eric_house is None or holly_house is None or int(eric_house) >= int(holly_house):
                    continue
                
                # Constraint 2: The person whose birthday is in April is in the first house
                if assignment[0]['birthday month'] != 'april':
                    continue
                
                # If all constraints are satisfied, return the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "birthday month", "mother's name"],
                        "rows": [
                            [assignment[0]['House'], assignment[0]['Name'], assignment[0]['birthday month'], assignment[0]["mother's name"]],
                            [assignment[1]['House'], assignment[1]['Name'], assignment[1]['birthday month'], assignment[1]["mother's name"]]
                        ]
                    }
                }
                return solution
    
    return {"solution": {}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))