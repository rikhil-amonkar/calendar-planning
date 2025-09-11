import itertools
import json

# Generate all possibilities and apply constraints
names_list = ['Arnold', 'Eric']
foods_list = ['grilled cheese', 'pizza']
mothers_list = ['Holly', 'Aniya']

valid_name_perms = []
for perm in itertools.permutations(names_list):
    if perm[1] != 'Arnold':  # Arnold not in house 2
        valid_name_perms.append(perm)

solution_found = None

for names in valid_name_perms:
    for food_perm in itertools.permutations(foods_list):
        if food_perm[0] == 'grilled cheese' and food_perm[1] == 'pizza':
            for mother_perm in itertools.permutations(mothers_list):
                if mother_perm[0] == 'Holly':
                    solution_found = [
                        ["1", names[0], food_perm[0], mother_perm[0]],
                        ["2", names[1], food_perm[1], mother_perm[1]]
                    ]
                    break
            if solution_found:
                break
    if solution_found:
        break

# Prepare JSON output
output = {
    "solution": {
        "header": ["House", "Name", "Food", "Mother"],
        "rows": solution_found
    }
}

print(json.dumps(output, indent=2))