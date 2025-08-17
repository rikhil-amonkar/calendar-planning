import itertools
import json

names = ['Arnold', 'Peter', 'Eric', 'Alice']
styles = ['victorian', 'ranch', 'colonial', 'craftsman']

valid_names = [perm for perm in itertools.permutations(names) if perm[2] == 'Eric' and perm[3] == 'Arnold']
valid_styles = [perm for perm in itertools.permutations(styles) if perm[2] == 'craftsman']

solution_found = None

for name_perm in valid_names:
    for style_perm in valid_styles:
        victorian_index = -1
        for i in range(3):
            if style_perm[i] == 'ranch' and style_perm[i+1] == 'victorian':
                victorian_index = i + 1
                break
        if victorian_index == -1:
            continue
        
        if name_perm[victorian_index] == 'Alice':
            solution = {
                "solution": {
                    "header": ["House", "Name", "HouseStyle"],
                    "rows": []
                }
            }
            for house_num in range(1, 5):
                idx = house_num - 1
                solution["solution"]["rows"].append([
                    str(house_num),
                    name_perm[idx],
                    style_perm[idx]
                ])
            solution_found = solution
            break
    if solution_found:
        break

print(json.dumps(solution_found))