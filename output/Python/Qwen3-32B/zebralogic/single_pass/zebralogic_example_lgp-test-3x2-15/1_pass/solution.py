import itertools
import json

# Define the possible names and attributes
names = ['Arnold', 'Peter', 'Eric']
heights = ['short', 'average', 'very short']

solution_found = None

for name_perm in itertools.permutations(names):
    for height_perm in itertools.permutations(heights):
        # Check clue 2: short in first house
        if height_perm[0] != 'short':
            continue
        
        # Check clue 3: one house between short and very short
        short_idx = height_perm.index('short')
        vs_idx = height_perm.index('very short')
        if abs(vs_idx - short_idx) != 2:
            continue
        
        # Check clue 1: Peter is to the right of Eric
        eric_idx = name_perm.index('Eric')
        peter_idx = name_perm.index('Peter')
        if peter_idx <= eric_idx:
            continue
        
        # Check clue 4: Arnold next to very short
        arnold_idx = name_perm.index('Arnold')
        vs_house = height_perm.index('very short')
        if abs(arnold_idx - vs_house) != 1:
            continue
        
        # If all clues are satisfied, this is the solution
        solution_found = {
            'solution': {
                'header': ['House', 'Name', 'Height'],
                'rows': [
                    [str(1), name_perm[0], height_perm[0]],
                    [str(2), name_perm[1], height_perm[1]],
                    [str(3), name_perm[2], height_perm[2]]
                ]
            }
        }
        # Break out of loops once solution is found
        break
    if solution_found:
        break

# Output the solution as JSON
print(json.dumps(solution_found))