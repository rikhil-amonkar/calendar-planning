import json
from itertools import permutations

def solve_puzzle():
    # Define the possible values for each attribute
    names = ['Eric', 'Arnold', 'Peter']
    heights = ['short', 'very short', 'average']
    
    # Generate all possible permutations for names and heights
    for name_perm in permutations(names):
        for height_perm in permutations(heights):
            # Assign to houses
            solution = [
                {'House': '1', 'Name': name_perm[0], 'Height': height_perm[0]},
                {'House': '2', 'Name': name_perm[1], 'Height': height_perm[1]},
                {'House': '3', 'Name': name_perm[2], 'Height': height_perm[2]}
            ]
            
            # Check all constraints
            # Constraint 1: Eric is not in the first house
            if solution[0]['Name'] == 'Eric':
                continue
            
            # Constraint 2: very short is left of short
            very_short_pos = None
            short_pos = None
            for i in range(3):
                if solution[i]['Height'] == 'very short':
                    very_short_pos = i
                if solution[i]['Height'] == 'short':
                    short_pos = i
            if very_short_pos is None or short_pos is None or very_short_pos >= short_pos:
                continue
            
            # Constraint 3: very short is Eric
            for house in solution:
                if house['Height'] == 'very short' and house['Name'] != 'Eric':
                    break
            else:
                # Constraint 4: Arnold is not in the first house
                if solution[0]['Name'] == 'Arnold':
                    continue
                
                # If all constraints are satisfied, format the solution
                output = {
                    "solution": {
                        "header": ["House", "Name", "Height"],
                        "rows": [
                            [house['House'], house['Name'], house['Height']] for house in solution
                        ]
                    }
                }
                return json.dumps(output)
    
    return json.dumps({"solution": {"header": ["House", "Name", "Height"], "rows": []}})

print(solve_puzzle())