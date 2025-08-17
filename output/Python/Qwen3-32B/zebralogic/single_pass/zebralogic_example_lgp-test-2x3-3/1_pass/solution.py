import itertools
import json

people = ['Arnold', 'Eric']
foods = ['grilled cheese', 'pizza']
mothers = ['Holly', 'Aniya']

for names in itertools.permutations(people):
    if names[1] == 'Arnold':
        continue  # Arnold cannot be in the second house
    for foods_perm in itertools.permutations(foods):
        if foods_perm[0] != 'grilled cheese' or foods_perm[1] != 'pizza':
            continue  # Grilled cheese must be directly left of pizza
        for mothers_perm in itertools.permutations(mothers):
            if mothers_perm[0] != 'Holly':
                continue  # Arnold's mother is Holly (house 1)
            solution = {
                "solution": {
                    "header": ["House", "Name", "Food", "Mother"],
                    "rows": [
                        ["1", names[0], foods_perm[0], mothers_perm[0]],
                        ["2", names[1], foods_perm[1], mothers_perm[1]],
                    ]
                }
            }
            print(json.dumps(solution))
            exit()