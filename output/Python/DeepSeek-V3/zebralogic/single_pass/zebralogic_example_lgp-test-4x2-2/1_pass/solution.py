import json
from itertools import permutations

def solve_puzzle():
    # Define the possible values for each attribute
    names = ['Arnold', 'Peter', 'Eric', 'Alice']
    house_styles = ['victorian', 'ranch', 'colonial', 'craftsman']
    houses = ['1', '2', '3', '4']
    
    # Initialize the solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": []
        }
    }
    
    # Generate all possible permutations of names and house styles
    for name_perm in permutations(names):
        for style_perm in permutations(house_styles):
            # Create a temporary assignment
            assignment = []
            for i in range(4):
                assignment.append({
                    'House': str(i+1),
                    'Name': name_perm[i],
                    'HouseStyle': style_perm[i]
                })
            
            # Check all constraints
            valid = True
            
            # Constraint 3: Eric is in the third house
            if assignment[2]['Name'] != 'Eric':
                valid = False
            
            # Constraint 4: Arnold is in the fourth house
            if assignment[3]['Name'] != 'Arnold':
                valid = False
            
            # Constraint 1: Eric is in a Craftsman-style house
            if assignment[2]['HouseStyle'] != 'craftsman':
                valid = False
            
            # Constraint 5: Alice is in the Victorian house
            alice_house = None
            for house in assignment:
                if house['Name'] == 'Alice':
                    alice_house = house
                    break
            if alice_house is None or alice_house['HouseStyle'] != 'victorian':
                valid = False
            
            # Constraint 2: Ranch is directly left of Victorian
            ranch_index = None
            victorian_index = None
            for i, house in enumerate(assignment):
                if house['HouseStyle'] == 'ranch':
                    ranch_index = i
                if house['HouseStyle'] == 'victorian':
                    victorian_index = i
            if ranch_index is None or victorian_index is None or ranch_index + 1 != victorian_index:
                valid = False
            
            if valid:
                # Prepare the rows for the solution
                rows = []
                for house in assignment:
                    rows.append([house['House'], house['Name'], house['HouseStyle']])
                solution["solution"]["rows"] = rows
                return json.dumps(solution, indent=2)
    
    return json.dumps(solution, indent=2)

print(solve_puzzle())