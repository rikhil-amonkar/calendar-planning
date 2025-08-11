import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    names = ['Eric', 'Arnold', 'Peter']
    heights = ['very short', 'short', 'average']
    houses = ['1', '2', '3']
    
    # Generate all possible permutations for names and heights
    for name_order in permutations(names):
        for height_order in permutations(heights):
            # Assign to houses
            solution = []
            for i in range(3):
                solution.append({
                    'House': str(i + 1),
                    'Name': name_order[i],
                    'Height': height_order[i]
                })
            
            # Check constraints
            # Constraint 1: Eric is not in the first house
            if solution[0]['Name'] == 'Eric':
                continue
            # Constraint 2: very short is left of short
            very_short_pos = None
            short_pos = None
            for i, house in enumerate(solution):
                if house['Height'] == 'very short':
                    very_short_pos = i
                if house['Height'] == 'short':
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
                # All constraints satisfied
                # Format the output
                output = {
                    "solution": {
                        "header": ["House", "Name", "Height"],
                        "rows": [
                            [house['House'], house['Name'], house['Height']] for house in solution
                        ]
                    }
                }
                return output
    return {"solution": {"header": [], "rows": []}}

# Solve and print the solution
solution = solve_puzzle()
print(json.dumps(solution, indent=2))