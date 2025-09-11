import itertools
import json

names = ['Bob', 'Peter', 'Eric', 'Alice', 'Arnold', 'Carol']
hair_colors = ['auburn', 'blonde', 'brown', 'black', 'red', 'gray']
heights = ['very tall', 'average', 'very short', 'tall', 'super tall', 'short']

for name_perm in itertools.permutations(names):
    if name_perm[3] != 'Alice':
        continue

    for hair_perm in itertools.permutations(hair_colors):
        if hair_perm[2] != 'gray':
            continue
        if hair_perm[3] == 'black':
            continue

        for height_perm in itertools.permutations(heights):
            if height_perm[4] != 'very short' or height_perm[5] != 'tall':
                continue

            # Check clue 8 and 13
            try:
                blonde_idx = hair_perm.index('blonde')
            except ValueError:
                continue
            if name_perm[blonde_idx] != 'Carol':
                continue
            if height_perm[blonde_idx] != 'very tall':
                continue

            # Check clue 1
            if blonde_idx + 1 >= 6:
                continue
            if name_perm[blonde_idx + 1] != 'Bob':
                continue

            # Check clue 11
            try:
                bob_idx = name_perm.index('Bob')
            except ValueError:
                continue
            if hair_perm[bob_idx] != 'brown':
                continue

            # Check clue 3
            try:
                arnold_idx = name_perm.index('Arnold')
            except ValueError:
                continue
            if height_perm[arnold_idx] != 'short':
                continue

            # Check clue 6
            try:
                red_idx = hair_perm.index('red')
            except ValueError:
                continue
            if name_perm[red_idx] != 'Eric':
                continue

            # Check clue 9
            if red_idx not in (0, 4):
                continue

            # Check clue 7
            try:
                average_idx = height_perm.index('average')
                super_tall_idx = height_perm.index('super tall')
            except ValueError:
                continue
            if super_tall_idx <= average_idx:
                continue

            # Build solution
            solution_rows = []
            for i in range(6):
                house_num = str(i + 1)
                name = name_perm[i]
                hair = hair_perm[i]
                height = height_perm[i]
                solution_rows.append([house_num, name, hair, height])

            solution = {
                "solution": {
                    "header": ["House", "Name", "HairColor", "Height"],
                    "rows": solution_rows
                }
            }

            print(json.dumps(solution))
            exit()