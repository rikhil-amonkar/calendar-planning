import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each attribute
    names = ['Arnold', 'Eric']
    months = ['april', 'sept']
    mothers = ['Aniya', 'Holly']
    
    # Generate all possible permutations for the two houses
    for name_perm in permutations(names):
        for month_perm in permutations(months):
            for mother_perm in permutations(mothers):
                # Assign attributes to houses
                solution = {
                    1: {
                        'Name': name_perm[0],
                        'Birthday': month_perm[0],
                        'Mother': mother_perm[0]
                    },
                    2: {
                        'Name': name_perm[1],
                        'Birthday': month_perm[1],
                        'Mother': mother_perm[1]
                    }
                }
                
                # Check all constraints
                # Constraint 1: Eric is left of the person whose mother is Holly
                eric_house = None
                holly_house = None
                for house in [1, 2]:
                    if solution[house]['Name'] == 'Eric':
                        eric_house = house
                    if solution[house]['Mother'] == 'Holly':
                        holly_house = house
                if eric_house is None or holly_house is None or eric_house >= holly_house:
                    continue
                
                # Constraint 2: April is in the first house
                if solution[1]['Birthday'] != 'april':
                    continue
                
                # If all constraints are satisfied, format the solution
                formatted_solution = {
                    "solution": {
                        "header": ["House", "Name", "Birthday", "Mother"],
                        "rows": [
                            ["1", solution[1]['Name'], solution[1]['Birthday'], solution[1]['Mother']],
                            ["2", solution[2]['Name'], solution[2]['Birthday'], solution[2]['Mother']]
                        ]
                    }
                }
                return formatted_solution
    
    return {"solution": {"header": [], "rows": []}}

# Solve and print the solution as JSON
solution = solve_puzzle()
print(json.dumps(solution, indent=2))