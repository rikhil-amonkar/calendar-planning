import itertools
import json

# Define the attributes
houses = [1, 2, 3]
names = ['Eric', 'Arnold', 'Peter']
heights = ['short', 'very short', 'average']

# Generate all permutations of names and heights
name_permutations = list(itertools.permutations(names))
height_permutations = list(itertools.permutations(heights))

# Function to check if a given arrangement satisfies all constraints
def is_valid(arrangement):
    name_arrangement, height_arrangement = arrangement
    
    # Constraint 1: Eric is not in the first house
    if name_arrangement[0] == 'Eric':
        return False
    
    # Constraint 4: Arnold is not in the first house
    if name_arrangement[0] == 'Arnold':
        return False
    
    # Constraint 3: The person who is very short is Eric
    if height_arrangement[name_arrangement.index('Eric')] != 'very short':
        return False
    
    # Constraint 2: The person who is very short is somewhere to the left of the person who is short
    very_short_index = height_arrangement.index('very short')
    short_index = height_arrangement.index('short')
    if very_short_index >= short_index:
        return False
    
    return True

# Find the valid arrangement
for name_perm in name_permutations:
    for height_perm in height_permutations:
        if is_valid((name_perm, height_perm)):
            # Construct the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Height"],
                    "rows": [
                        [str(houses[0]), name_perm[0], height_perm[0]],
                        [str(houses[1]), name_perm[1], height_perm[1]],
                        [str(houses[2]), name_perm[2], height_perm[2]]
                    ]
                }
            }
            break

# Output the solution as JSON
print(json.dumps(solution, indent=2))