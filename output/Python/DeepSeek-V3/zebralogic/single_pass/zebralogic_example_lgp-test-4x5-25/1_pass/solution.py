import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    categories = {
        'House': ['1', '2', '3', '4'],
        'Name': ['Arnold', 'Peter', 'Eric', 'Alice'],
        'House Style': ['craftsman', 'colonial', 'victorian', 'ranch'],
        'Hair Color': ['red', 'blonde', 'black', 'brown'],
        'Child': ['Bella', 'Fred', 'Meredith', 'Samantha'],
        'Favorite Book Genre': ['mystery', 'fantasy', 'romance', 'science fiction']
    }
    
    # Generate all possible permutations for each category except House (fixed order)
    for names in permutations(categories['Name']):
        for styles in permutations(categories['House Style']):
            for hair_colors in permutations(categories['Hair Color']):
                for children in permutations(categories['Child']):
                    for genres in permutations(categories['Favorite Book Genre']):
                        # Create a dictionary to hold the current assignment
                        assignment = {
                            'House': categories['House'],
                            'Name': list(names),
                            'House Style': list(styles),
                            'Hair Color': list(hair_colors),
                            'Child': list(children),
                            'Favorite Book Genre': list(genres)
                        }
                        
                        # Check all constraints
                        # Constraint 1: Craftsman is house 3
                        if assignment['House Style'][2] != 'craftsman':
                            continue
                        
                        # Constraint 2: Alice loves romance
                        alice_index = assignment['Name'].index('Alice')
                        if assignment['Favorite Book Genre'][alice_index] != 'romance':
                            continue
                        
                        # Constraint 3: Brown hair is house 4
                        if assignment['Hair Color'][3] != 'brown':
                            continue
                        
                        # Constraint 4: Child Samantha is house 4
                        if assignment['Child'][3] != 'Samantha':
                            continue
                        
                        # Constraint 5: Ranch is right of red hair
                        red_hair_index = assignment['Hair Color'].index('red')
                        ranch_indices = [i for i, style in enumerate(assignment['House Style']) if style == 'ranch']
                        if not ranch_indices or ranch_indices[0] <= red_hair_index:
                            continue
                        
                        # Constraint 6: Peter's child is Bella
                        if 'Peter' in assignment['Name']:
                            peter_index = assignment['Name'].index('Peter')
                            if assignment['Child'][peter_index] != 'Bella':
                                continue
                        
                        # Constraint 7: Arnold has red hair
                        if 'Arnold' in assignment['Name']:
                            arnold_index = assignment['Name'].index('Arnold')
                            if assignment['Hair Color'][arnold_index] != 'red':
                                continue
                        
                        # Constraint 8: Alice is in colonial
                        if assignment['House Style'][alice_index] != 'colonial':
                            continue
                        
                        # Constraint 9: Black hair is house 2
                        if assignment['Hair Color'][1] != 'black':
                            continue
                        
                        # Constraint 10: Peter loves fantasy
                        if 'Peter' in assignment['Name']:
                            peter_index = assignment['Name'].index('Peter')
                            if assignment['Favorite Book Genre'][peter_index] != 'fantasy':
                                continue
                        
                        # Constraint 11: Arnold's child is Meredith
                        if 'Arnold' in assignment['Name']:
                            arnold_index = assignment['Name'].index('Arnold')
                            if assignment['Child'][arnold_index] != 'Meredith':
                                continue
                        
                        # Constraint 12: Black hair is Eric
                        black_hair_index = assignment['Hair Color'].index('black')
                        if assignment['Name'][black_hair_index] != 'Eric':
                            continue
                        
                        # Constraint 13: Arnold loves science fiction
                        if 'Arnold' in assignment['Name']:
                            arnold_index = assignment['Name'].index('Arnold')
                            if assignment['Favorite Book Genre'][arnold_index] != 'science fiction':
                                continue
                        
                        # If all constraints passed, prepare the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "House Style", "Hair Color", "Child", "Favorite Book Genre"],
                                "rows": []
                            }
                        }
                        
                        for i in range(4):
                            row = [
                                assignment['House'][i],
                                assignment['Name'][i],
                                assignment['House Style'][i],
                                assignment['Hair Color'][i],
                                assignment['Child'][i],
                                assignment['Favorite Book Genre'][i]
                            ]
                            solution["solution"]["rows"].append(row)
                        
                        return solution
    
    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the JSON result
solution = solve_puzzle()
print(json.dumps(solution, indent=2))