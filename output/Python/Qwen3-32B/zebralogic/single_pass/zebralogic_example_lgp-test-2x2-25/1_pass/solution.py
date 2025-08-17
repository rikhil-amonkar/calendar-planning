import itertools
import json

# Generate all permutations for names and vacations
names = ['Arnold', 'Eric']
vacations = ['beach', 'mountain']

for name_perm in itertools.permutations(names):
    for vac_perm in itertools.permutations(vacations):
        # Find beach house number (1-based)
        beach_house = None
        for idx, v in enumerate(vac_perm):
            if v == 'beach':
                beach_house = idx + 1
                break
        # Find Arnold's house number
        arnold_house = None
        for idx, n in enumerate(name_perm):
            if n == 'Arnold':
                arnold_house = idx + 1
                break
        # Check the constraint
        if arnold_house > beach_house:
            # Valid solution found
            rows = []
            for i in range(2):
                house_num = str(i + 1)
                rows.append([
                    house_num,
                    name_perm[i],
                    vac_perm[i]
                ])
            solution = {
                "solution": {
                    "header": ["House", "Name", "Vacation"],
                    "rows": rows
                }
            }
            print(json.dumps(solution))
            exit()