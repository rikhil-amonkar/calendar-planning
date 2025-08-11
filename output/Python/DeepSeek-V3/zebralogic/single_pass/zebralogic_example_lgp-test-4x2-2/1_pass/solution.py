import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    names = ['Arnold', 'Peter', 'Eric', 'Alice']
    styles = ['victorian', 'ranch', 'colonial', 'craftsman']
    houses = ['1', '2', '3', '4']
    
    # Initialize the solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "style"],
            "rows": []
        }
    }
    
    # Generate all possible permutations for names and styles
    for name_perm in permutations(names):
        for style_perm in permutations(styles):
            # Assign to houses
            assignment = [
                {'House': '1', 'Name': name_perm[0], 'style': style_perm[0]},
                {'House': '2', 'Name': name_perm[1], 'style': style_perm[1]},
                {'House': '3', 'Name': name_perm[2], 'style': style_perm[2]},
                {'House': '4', 'Name': name_perm[3], 'style': style_perm[3]}
            ]
            
            # Check all constraints
            # Constraint 3: Eric is in the third house
            if assignment[2]['Name'] != 'Eric':
                continue
            
            # Constraint 1: Eric is in a craftsman house
            if assignment[2]['style'] != 'craftsman':
                continue
            
            # Constraint 4: Arnold is in the fourth house
            if assignment[3]['Name'] != 'Arnold':
                continue
            
            # Constraint 5: Alice is in Victorian house
            alice_house = None
            for house in assignment:
                if house['Name'] == 'Alice':
                    alice_house = house
                    break
            if alice_house is None or alice_house['style'] != 'victorian':
                continue
            
            # Constraint 2: ranch is directly left of victorian
            ranch_pos = None
            victorian_pos = None
            for i, house in enumerate(assignment):
                if house['style'] == 'ranch':
                    ranch_pos = i
                if house['style'] == 'victorian':
                    victorian_pos = i
            if ranch_pos is None or victorian_pos is None or ranch_pos + 1 != victorian_pos:
                continue
            
            # All constraints satisfied, build the solution
            for house in assignment:
                row = [
                    house['House'],
                    house['Name'],
                    house['style']
                ]
                solution["solution"]["rows"].append(row)
            
            # Return the first valid solution
            return solution
    
    return solution

# Solve the puzzle and print the JSON
solution = solve_puzzle()
print(json.dumps(solution, indent=2))