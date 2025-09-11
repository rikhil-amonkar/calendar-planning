import itertools
import json

names = ['Peter', 'Arnold', 'Alice', 'Eric']
colors = ['yellow', 'green', 'red', 'white']

solution = None

for name_perm in itertools.permutations(['Arnold', 'Alice', 'Eric']):
    current_names = ['Peter'] + list(name_perm)
    for color_perm in itertools.permutations(['yellow', 'red', 'white']):
        current_colors = [color_perm[0], color_perm[1], 'green', color_perm[2]]
        # Check Arnold is directly left of Eric
        arnold_idx = current_names.index('Arnold')
        eric_idx = current_names.index('Eric')
        if arnold_idx + 1 != eric_idx:
            continue
        # Check Eric's color is yellow
        if current_colors[eric_idx] != 'yellow':
            continue
        # Check red and yellow positions
        red_idx = current_colors.index('red')
        yellow_idx = current_colors.index('yellow')
        if abs(red_idx - yellow_idx) != 2:
            continue
        # Build solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Color"],
                "rows": []
            }
        }
        for i in range(4):
            house_num = str(i + 1)
            name = current_names[i]
            color = current_colors[i]
            solution["solution"]["rows"].append([house_num, name, color])
        break  # exit color_perm loop
    if solution:
        break  # exit name_perm loop

print(json.dumps(solution))