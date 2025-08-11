import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    houses = ['1', '2']
    names = ['Eric', 'Arnold']
    children = ['Bella', 'Fred']
    lunches = ['grilled cheese', 'pizza']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for child_perm in permutations(children):
            for lunch_perm in permutations(lunches):
                # Assign attributes to houses
                solution = {
                    '1': {
                        'House': '1',
                        'Name': name_perm[0],
                        'Child': child_perm[0],
                        'Lunch': lunch_perm[0]
                    },
                    '2': {
                        'House': '2',
                        'Name': name_perm[1],
                        'Child': child_perm[1],
                        'Lunch': lunch_perm[1]
                    }
                }
                
                # Check Clue 1: The person who is a pizza lover is Arnold.
                clue1_passed = True
                for house in ['1', '2']:
                    if solution[house]['Lunch'] == 'pizza' and solution[house]['Name'] != 'Arnold':
                        clue1_passed = False
                        break
                if not clue1_passed:
                    continue
                
                # Check Clue 2: The person who loves eating grilled cheese is directly left of the person's child is named Fred.
                # Since there are only 2 houses, house 1 must be grilled cheese and house 2's child must be Fred
                if solution['1']['Lunch'] == 'grilled cheese' and solution['2']['Child'] == 'Fred':
                    # Prepare the output
                    output = {
                        "solution": {
                            "header": ["House", "Name", "Child", "Lunch"],
                            "rows": [
                                [solution['1']['House'], solution['1']['Name'], solution['1']['Child'], solution['1']['Lunch']],
                                [solution['2']['House'], solution['2']['Name'], solution['2']['Child'], solution['2']['Lunch']]
                            ]
                        }
                    }
                    return output
    
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))