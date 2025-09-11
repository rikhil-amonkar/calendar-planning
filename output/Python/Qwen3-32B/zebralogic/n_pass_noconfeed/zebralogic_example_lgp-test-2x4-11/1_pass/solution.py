import itertools
import json

# Define the possible values
names = ['Eric', 'Arnold']
hobbies = ['gardening', 'photography']
pets = ['cat', 'dog']
heights = ['short', 'very short']

solution_found = None

# Generate all permutations for each category
name_perms = list(itertools.permutations(names))
hobby_perms = list(itertools.permutations(hobbies))
pet_perms = list(itertools.permutations(pets))
height_perms = list(itertools.permutations(heights))

# Iterate through all possible combinations of permutations
for n_p in name_perms:
    for h_p in hobby_perms:
        for p_p in pet_perms:
            for ht_p in height_perms:
                # Create the houses
                houses = [
                    (n_p[0], h_p[0], p_p[0], ht_p[0]),
                    (n_p[1], h_p[1], p_p[1], ht_p[1]),
                ]
                
                # Check constraint 2: Eric is very short
                eric_index = None
                for i in range(2):
                    if houses[i][0] == 'Eric':
                        eric_index = i
                        break
                if eric_index is None:
                    continue
                if houses[eric_index][3] != 'very short':
                    continue
                
                # Check constraint 1: Eric's hobby is photography
                if houses[eric_index][1] != 'photography':
                    continue
                
                # Check constraint 3: cat is to the right of very short (Eric's house)
                cat_index = None
                for i in range(2):
                    if houses[i][2] == 'cat':
                        cat_index = i
                        break
                if cat_index is None:
                    continue
                if cat_index <= eric_index:
                    continue
                
                # If all constraints are satisfied
                solution_found = houses
                break
            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break

# Now build the JSON structure
if solution_found:
    rows = []
    for i in range(2):
        house_num = str(i + 1)
        name = solution_found[i][0]
        hobby = solution_found[i][1]
        pet = solution_found[i][2]
        height = solution_found[i][3]
        rows.append([house_num, name, hobby, pet, height])
    json_output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Pet", "Height"],
            "rows": rows
        }
    }
    print(json.dumps(json_output, indent=2))
else:
    print(json.dumps({"solution": "No solution found"}))