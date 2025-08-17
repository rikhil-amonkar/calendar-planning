import itertools
import json

# Generate all possible permutations for names and colors
for name_perm in itertools.permutations(['Arnold', 'Alice', 'Eric']):
    names = ['Peter', name_perm[0], name_perm[1], name_perm[2]]
    for color_perm in itertools.permutations(['yellow', 'red', 'white']):
        colors = [color_perm[0], color_perm[1], 'green', color_perm[2]]
        
        # Check if Eric's color is yellow
        eric_index = names.index('Eric')
        if colors[eric_index] != 'yellow':
            continue
        
        # Check if Arnold is directly left of Eric
        arnold_index = names.index('Arnold')
        if arnold_index + 1 != eric_index:
            continue
        
        # Check if red and yellow have one house between them
        red_pos = -1
        yellow_pos = -1
        for i in range(4):
            if colors[i] == 'red':
                red_pos = i
            if colors[i] == 'yellow':
                yellow_pos = i
        if abs(red_pos - yellow_pos) != 2:
            continue
        
        # Build the solution JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "Color"],
                "rows": []
            }
        }
        for i in range(4):
            house_num = i + 1
            solution["solution"]["rows"].append([
                str(house_num), names[i], colors[i]
            ])
        
        # Output the JSON and exit
        print(json.dumps(solution))
        exit()