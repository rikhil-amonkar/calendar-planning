import itertools
import json

names = ['Arnold', 'Peter', 'Eric']
heights = ['short', 'average', 'very short']

for name_perm in itertools.permutations(names):
    for height_perm in itertools.permutations(heights):
        # Check clue 2: The person who is short is in the first house
        if height_perm[0] != 'short':
            continue
        # Check clue 3: One house between short and very short
        if height_perm[2] != 'very short':
            continue
        # Check clue 4: Arnold and the very short are next to each other
        if name_perm[1] != 'Arnold':
            continue
        # Check clue 1: Peter is to the right of Eric
        eric_pos = name_perm.index('Eric')
        peter_pos = name_perm.index('Peter')
        if eric_pos < peter_pos:
            solution_data = {
                "solution": {
                    "header": ["House", "Name", "Height"],
                    "rows": []
                }
            }
            for i in range(3):
                house_num = str(i + 1)
                name = name_perm[i]
                height = height_perm[i]
                solution_data['solution']['rows'].append([house_num, name, height])
            print(json.dumps(solution_data))
            break