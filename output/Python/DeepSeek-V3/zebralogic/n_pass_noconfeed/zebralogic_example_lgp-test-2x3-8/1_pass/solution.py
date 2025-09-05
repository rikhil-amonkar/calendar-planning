import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Arnold', 'Eric']
    birthdays = ['april', 'sept']
    mothers = ['Aniya', 'Holly']
    
    # Generate all possible permutations for each house
    for name_perm in permutations(names):
        for bday_perm in permutations(birthdays):
            for mother_perm in permutations(mothers):
                # Create assignment for house 1 and 2
                assignment = {
                    1: {'Name': name_perm[0], 'Birthday': bday_perm[0], 'Mother': mother_perm[0]},
                    2: {'Name': name_perm[1], 'Birthday': bday_perm[1], 'Mother': mother_perm[1]}
                }
                
                # Check clue 1: Eric is somewhere to the left of the person whose mother's name is Holly
                eric_house = None
                holly_mother_house = None
                
                for house in [1, 2]:
                    if assignment[house]['Name'] == 'Eric':
                        eric_house = house
                    if assignment[house]['Mother'] == 'Holly':
                        holly_mother_house = house
                
                # Eric must be left of Holly mother (smaller house number)
                if eric_house is None or holly_mother_house is None or eric_house >= holly_mother_house:
                    continue
                
                # Check clue 2: The person whose birthday is in April is in the first house
                if assignment[1]['Birthday'] != 'april':
                    continue
                
                # If we reach here, all constraints are satisfied
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Birthday", "Mother"],
                        "rows": [
                            ["1", assignment[1]['Name'], assignment[1]['Birthday'], assignment[1]['Mother']],
                            ["2", assignment[2]['Name'], assignment[2]['Birthday'], assignment[2]['Mother']]
                        ]
                    }
                }
                return solution
    
    return {"solution": {"header": ["House", "Name", "Birthday", "Mother"], "rows": []}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))