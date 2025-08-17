import itertools
import json

# Define the possible values
names = ['Eric', 'Arnold']
birthdays = ['april', 'sept']  # Fixed by clue 2
colors = ['yellow', 'red']

# Generate all possible permutations for names and colors
name_perms = list(itertools.permutations(names))
color_perms = list(itertools.permutations(colors))

solution_found = None

for name_perm in name_perms:
    for color_perm in color_perms:
        # Check if Eric is in house 1 (violates clue 3)
        if name_perm[0] == 'Eric':
            continue
        
        # Check if Eric's color is yellow (clue 1)
        eric_house = 1 if name_perm[0] == 'Eric' else 2
        if name_perm[1] == 'Eric' and color_perm[1] != 'yellow':
            continue
        
        # If all constraints are satisfied
        solution_found = (name_perm, color_perm)
        break
    if solution_found:
        break

# Build the solution structure
if solution_found:
    name_perm, color_perm = solution_found
    rows = []
    for i in range(2):
        house_num = str(i + 1)
        name = name_perm[i]
        birthday = birthdays[i]
        color = color_perm[i]
        rows.append([house_num, name, birthday, color])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print(json.dumps({"solution": "No solution found"}))