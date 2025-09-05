import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ['Peter', 'Arnold', 'Alice', 'Eric']
    colors = ['yellow', 'green', 'red', 'white']
    houses = ['1', '2', '3', '4']
    
    # Generate all possible permutations
    name_perms = list(permutations(names))
    color_perms = list(permutations(colors))
    
    # Try all combinations
    for name_assignment in name_perms:
        for color_assignment in color_perms:
            # Create house assignments
            assignment = {}
            for i in range(4):
                house_num = str(i + 1)
                assignment[house_num] = {
                    'name': name_assignment[i],
                    'color': color_assignment[i]
                }
            
            # Check all constraints
            # Clue 1: Green color is in third house
            if assignment['3']['color'] != 'green':
                continue
            
            # Clue 2: Peter is in first house
            if assignment['1']['name'] != 'Peter':
                continue
            
            # Clue 4: Arnold is directly left of Eric
            arnold_house = None
            eric_house = None
            for house_num in houses:
                if assignment[house_num]['name'] == 'Arnold':
                    arnold_house = int(house_num)
                if assignment[house_num]['name'] == 'Eric':
                    eric_house = int(house_num)
            
            if arnold_house is None or eric_house is None or eric_house - arnold_house != 1:
                continue
            
            # Clue 5: Eric loves yellow
            if assignment[str(eric_house)]['color'] != 'yellow':
                continue
            
            # Clue 3: One house between red and yellow
            red_house = None
            yellow_house = None
            for house_num in houses:
                if assignment[house_num]['color'] == 'red':
                    red_house = int(house_num)
                if assignment[house_num]['color'] == 'yellow':
                    yellow_house = int(house_num)
            
            if abs(red_house - yellow_house) != 2:
                continue
            
            # If we reach here, all constraints are satisfied
            # Format the solution
            rows = []
            for house_num in houses:
                rows.append([house_num, assignment[house_num]['name'], assignment[house_num]['color']])
            
            result = {
                "solution": {
                    "header": ["House", "Name", "Color"],
                    "rows": rows
                }
            }
            
            return json.dumps(result, indent=2)
    
    return json.dumps({"error": "No solution found"})

if __name__ == "__main__":
    print(solve_puzzle())