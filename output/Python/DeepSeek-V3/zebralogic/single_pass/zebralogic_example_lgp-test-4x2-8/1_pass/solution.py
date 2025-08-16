import json
from itertools import permutations

def solve_puzzle():
    # Define the possible values for each attribute
    names = ['Peter', 'Arnold', 'Alice', 'Eric']
    colors = ['yellow', 'green', 'red', 'white']
    houses = ['1', '2', '3', '4']
    
    # Generate all possible permutations for names and colors
    for name_perm in permutations(names):
        for color_perm in permutations(colors):
            solution = {
                '1': {'Name': name_perm[0], 'Color': color_perm[0]},
                '2': {'Name': name_perm[1], 'Color': color_perm[1]},
                '3': {'Name': name_perm[2], 'Color': color_perm[2]},
                '4': {'Name': name_perm[3], 'Color': color_perm[3]},
            }
            
            # Check all constraints
            # Constraint 1: Green is in house 3
            if solution['3']['Color'] != 'green':
                continue
            
            # Constraint 2: Peter is in house 1
            if solution['1']['Name'] != 'Peter':
                continue
            
            # Constraint 4: Arnold is directly left of Eric
            arnold_pos = None
            eric_pos = None
            for house in houses:
                if solution[house]['Name'] == 'Arnold':
                    arnold_pos = int(house)
                if solution[house]['Name'] == 'Eric':
                    eric_pos = int(house)
            if arnold_pos is None or eric_pos is None or eric_pos != arnold_pos + 1:
                continue
            
            # Constraint 5: Eric loves yellow
            if solution[str(eric_pos)]['Color'] != 'yellow':
                continue
            
            # Constraint 3: One house between red and yellow
            red_pos = None
            yellow_pos = None
            for house in houses:
                if solution[house]['Color'] == 'red':
                    red_pos = int(house)
                if solution[house]['Color'] == 'yellow':
                    yellow_pos = int(house)
            if red_pos is None or yellow_pos is None:
                continue
            if abs(red_pos - yellow_pos) != 2:
                continue
            
            # If all constraints are satisfied, format the solution
            result = {
                "solution": {
                    "header": ["House", "Name", "Color"],
                    "rows": [
                        ["1", solution['1']['Name'], solution['1']['Color']],
                        ["2", solution['2']['Name'], solution['2']['Color']],
                        ["3", solution['3']['Name'], solution['3']['Color']],
                        ["4", solution['4']['Name'], solution['4']['Color']]
                    ]
                }
            }
            return json.dumps(result, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())