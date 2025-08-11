import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    names = ['Peter', 'Arnold', 'Alice', 'Eric']
    colors = ['yellow', 'green', 'red', 'white']
    
    # Initialize houses
    houses = [1, 2, 3, 4]
    solution = []
    
    # Generate all possible permutations of names and colors
    for name_perm in permutations(names):
        for color_perm in permutations(colors):
            # Assign names and colors to houses
            assignment = []
            for i in range(4):
                assignment.append({
                    'House': str(i + 1),
                    'Name': name_perm[i],
                    'Color': color_perm[i]
                })
            
            # Check all constraints
            valid = True
            
            # Constraint 1: Green is in house 3
            if assignment[2]['Color'] != 'green':
                valid = False
            
            # Constraint 2: Peter is in house 1
            if assignment[0]['Name'] != 'Peter':
                valid = False
            
            # Constraint 3: One house between red and yellow
            red_pos = None
            yellow_pos = None
            for i in range(4):
                if assignment[i]['Color'] == 'red':
                    red_pos = i + 1
                if assignment[i]['Color'] == 'yellow':
                    yellow_pos = i + 1
            if red_pos is None or yellow_pos is None or abs(red_pos - yellow_pos) != 2:
                valid = False
            
            # Constraint 4: Arnold is directly left of Eric
            arnold_pos = None
            eric_pos = None
            for i in range(4):
                if assignment[i]['Name'] == 'Arnold':
                    arnold_pos = i + 1
                if assignment[i]['Name'] == 'Eric':
                    eric_pos = i + 1
            if arnold_pos is None or eric_pos is None or eric_pos - arnold_pos != 1:
                valid = False
            
            # Constraint 5: Eric loves yellow
            if eric_pos is not None and assignment[eric_pos - 1]['Color'] != 'yellow':
                valid = False
            
            if valid:
                solution = assignment
                break
        if solution:
            break
    
    # Prepare the output
    output = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": []
        }
    }
    
    for house in solution:
        output["solution"]["rows"].append([
            house['House'],
            house['Name'],
            house['Color']
        ])
    
    return json.dumps(output, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())