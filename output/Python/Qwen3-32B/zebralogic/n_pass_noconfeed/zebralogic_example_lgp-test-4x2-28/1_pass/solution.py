import itertools
import json

# Define the possible names and hair colors
names = ['Alice', 'Arnold', 'Peter', 'Eric']
hair_colors = ['black', 'blonde', 'brown', 'red']

solution = None

# Generate all valid name permutations (starting with Alice, followed by Arnold)
for name_perm in itertools.permutations(names):
    if name_perm[0] == 'Alice' and name_perm[1] == 'Arnold':
        # Find Eric's position
        eric_pos = name_perm.index('Eric')
        # Check if Eric can satisfy clue 1 (has a house to the right)
        if eric_pos == 3:
            continue  # No house to the right, skip this permutation
        # Check for hair color permutations
        for hair_perm in itertools.permutations(hair_colors):
            # Clue 3: Eric has brown hair
            if hair_perm[eric_pos] != 'brown':
                continue
            # Clue 1: Eric is directly left of blonde hair
            if hair_perm[eric_pos + 1] != 'blonde':
                continue
            # Clue 4: Black hair not in first house
            if hair_perm[0] == 'black':
                continue
            # All constraints satisfied
            solution = {
                "solution": {
                    "header": ["House", "Name", "HairColor"],
                    "rows": []
                }
            }
            for i in range(4):
                house = str(i + 1)
                name = name_perm[i]
                color = hair_perm[i]
                solution["solution"]["rows"].append([house, name, color])
            # Break out of loops once solution is found
            break
        if solution:
            break

# Output the solution as JSON
print(json.dumps(solution, indent=2))