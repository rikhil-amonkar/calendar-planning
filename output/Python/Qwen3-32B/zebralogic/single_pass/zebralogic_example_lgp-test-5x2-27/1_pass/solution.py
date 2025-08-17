import itertools
import json

names = ['Peter', 'Alice', 'Bob', 'Eric', 'Arnold']
heights = ['very tall', 'average', 'tall', 'very short', 'short']

solution_found = None

for name_perm in itertools.permutations(names):
    if name_perm[3] != 'Alice':
        continue

    for height_perm in itertools.permutations(heights):
        if height_perm[1] != 'short' or height_perm[4] != 'average':
            continue
        if height_perm[0] != 'very short' and height_perm[2] != 'very short':
            continue

        peter_idx = name_perm.index('Peter')
        bob_idx = name_perm.index('Bob')
        if bob_idx != peter_idx + 1:
            continue

        eric_idx = name_perm.index('Eric')
        if eric_idx >= peter_idx:
            continue

        very_tall_idx = height_perm.index('very tall')
        if very_tall_idx + 1 != peter_idx:
            continue

        rows = []
        for i in range(5):
            house_num = str(i + 1)
            name = name_perm[i]
            height = height_perm[i]
            rows.append([house_num, name, height])

        solution_found = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": rows
            }
        }
        break
    if solution_found:
        break

print(json.dumps(solution_found))