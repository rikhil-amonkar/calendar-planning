import json
from itertools import permutations

# Define the possible values for each category
people = ['Eric', 'Arnold']
foods = ['pizza', 'grilled cheese']

# Find valid name arrangement: Arnold is not in the first house
valid_names = None
for perm in permutations(people):
    if perm[0] != 'Arnold':
        valid_names = perm
        break

# Find valid food arrangement: Pizza is in the second house
valid_foods = None
for perm in permutations(foods):
    if perm[1] == 'pizza':
        valid_foods = perm
        break

# Construct the solution in the required format
solution = {
    "solution": {
        "header": ["House", "Name", "Food"],
        "rows": [
            ["1", valid_names[0], valid_foods[0]],
            ["2", valid_names[1], valid_foods[1]]
        ]
    }
}

# Output the solution as JSON
print(json.dumps(solution))