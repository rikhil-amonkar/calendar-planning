import json

def solve_puzzle():
    # Define possible values for each attribute
    names = ['Arnold', 'Eric']
    foods = ['grilled cheese', 'pizza']
    mothers = ['Holly', 'Aniya']
    
    # Initialize possible houses
    houses = [1, 2]
    solution = []
    
    # Generate all possible permutations
    from itertools import permutations, product
    
    # Try all possible assignments
    for name_perm in permutations(names):
        for food_perm in permutations(foods):
            for mother_perm in permutations(mothers):
                # Assign to houses
                assignment = [
                    {'House': '1', 'Name': name_perm[0], 'Food': food_perm[0], 'Mother': mother_perm[0]},
                    {'House': '2', 'Name': name_perm[1], 'Food': food_perm[1], 'Mother': mother_perm[1]}
                ]
                
                # Check constraints
                # Clue 1: grilled cheese is directly left of pizza
                if not (assignment[0]['Food'] == 'grilled cheese' and assignment[1]['Food'] == 'pizza'):
                    continue
                
                # Clue 2: Arnold is not in the second house
                if assignment[1]['Name'] == 'Arnold':
                    continue
                
                # Clue 3: Arnold's mother is Holly
                for house in assignment:
                    if house['Name'] == 'Arnold' and house['Mother'] != 'Holly':
                        break
                else:
                    # All constraints satisfied
                    solution = assignment
                    break
            if solution:
                break
        if solution:
            break
    
    # Prepare output
    output = {
        "solution": {
            "header": ["House", "Name", "Food", "Mother"],
            "rows": [
                [solution[0]['House'], solution[0]['Name'], solution[0]['Food'], solution[0]['Mother']],
                [solution[1]['House'], solution[1]['Name'], solution[1]['Food'], solution[1]['Mother']]
            ]
        }
    }
    
    return json.dumps(output)

print(solve_puzzle())