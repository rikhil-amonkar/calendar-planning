import itertools
import json

# Define the possible attributes
names = ['Eric', 'Arnold']
foods = ['pizza', 'grilled cheese']

solution_found = None

# Generate all permutations for names and foods
for name_perm in itertools.permutations(names):
    for food_perm in itertools.permutations(foods):
        # Check clue 1: pizza lover is in the second house
        if food_perm[1] != 'pizza':
            continue
        # Check clue 2: Arnold is not in the first house
        if name_perm[0] == 'Arnold':
            continue
        # Build solution rows if constraints are satisfied
        rows = [
            ["1", name_perm[0], food_perm[0]],
            ["2", name_perm[1], food_perm[1]]
        ]
        solution_found = rows
        break
    if solution_found:
        break

# Construct the JSON output
result = {
    "solution": {
        "header": ["House", "Name", "Food"],
        "rows": solution_found
    }
}

# Print the JSON-formatted solution
print(json.dumps(result, indent=2))