import itertools
import json

# Define the possible names and hair colors
names_list = ['Alice', 'Arnold', 'Peter', 'Eric']
hair_colors_list = ['black', 'blonde', 'brown', 'red']

# Generate all possible name permutations where Alice is in house 1
valid_name_perms = []
for perm in itertools.permutations(['Arnold', 'Peter', 'Eric']):
    names = ['Alice', perm[0], perm[1], perm[2]]
    # Check if Alice and Arnold are next to each other (Arnold must be in house 2)
    if names[1] == 'Arnold':
        valid_name_perms.append(names)

# Now check for each valid name permutation and hair color permutations
solution_found = None

for names in valid_name_perms:
    for hair_colors in itertools.permutations(hair_colors_list):
        # Check if Eric has brown hair
        eric_pos = names.index('Eric')
        if hair_colors[eric_pos] != 'brown':
            continue
        
        # Check if Eric is directly left of the person with blonde hair
        if eric_pos + 1 >= 4:  # Eric can't be in the last house
            continue
        if hair_colors[eric_pos + 1] != 'blonde':
            continue
        
        # Check that black hair is not in the first house
        if hair_colors[0] == 'black':
            continue
        
        # All constraints are satisfied
        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor"],
                "rows": []
            }
        }
        for i in range(4):
            house_num = i + 1
            name = names[i]
            hair_color = hair_colors[i]
            solution['solution']['rows'].append([str(house_num), name, hair_color])
        
        solution_found = solution
        # Assuming only one solution, break early
        break
    if solution_found:
        break

# Output the JSON
print(json.dumps(solution_found))