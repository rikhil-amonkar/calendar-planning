import itertools
import json

# Define the possible names and heights
names = ['Eric', 'Arnold', 'Peter']
heights = ['short', 'very short', 'average']

solution_data = None

# Iterate through all permutations of names and heights
for name_perm in itertools.permutations(names):
    # Skip if Eric or Arnold is in the first house (Constraint 1 and 4)
    if name_perm[0] == 'Eric' or name_perm[0] == 'Arnold':
        continue
    
    for height_perm in itertools.permutations(heights):
        # Constraint 3: Eric is very short
        eric_index = name_perm.index('Eric')
        if height_perm[eric_index] != 'very short':
            continue
        
        # Constraint 2: very short is left of short
        vshort_pos = height_perm.index('very short')
        short_pos = height_perm.index('short')
        if vshort_pos >= short_pos:
            continue
        
        # Build the solution if all constraints are satisfied
        rows = []
        for i in range(3):
            house = str(i + 1)
            name = name_perm[i]
            height = height_perm[i]
            rows.append([house, name, height])
        
        solution_data = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": rows
            }
        }
        # Break loops once solution is found
        break
    if solution_data:
        break

# Output the solution as JSON
print(json.dumps(solution_data, indent=2))