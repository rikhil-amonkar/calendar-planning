import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes and their possible values
    attributes = {
        'Name': ['Eric', 'Arnold'],
        'birthday month': ['sept', 'april'],
        'color': ['yellow', 'red']
    }
    
    # Houses are fixed as 1 and 2
    houses = [1, 2]
    
    # Generate all possible permutations for each attribute
    name_perms = permutations(attributes['Name'])
    month_perms = permutations(attributes['birthday month'])
    color_perms = permutations(attributes['color'])
    
    # Iterate through all possible combinations of permutations
    for names in name_perms:
        for months in month_perms:
            for colors in color_perms:
                # Assign attributes to houses
                assignment = []
                for i in range(2):
                    house = {
                        'House': str(i + 1),
                        'Name': names[i],
                        'birthday month': months[i],
                        'color': colors[i]
                    }
                    assignment.append(house)
                
                # Check constraints
                # Constraint 1: Eric loves yellow
                eric_yellow = True
                for house in assignment:
                    if house['Name'] == 'Eric' and house['color'] != 'yellow':
                        eric_yellow = False
                        break
                if not eric_yellow:
                    continue
                
                # Constraint 2: April birthday is in house 1
                april_house1 = assignment[0]['birthday month'] == 'april'
                if not april_house1:
                    continue
                
                # Constraint 3: Yellow is not in house 1
                yellow_not_house1 = assignment[0]['color'] != 'yellow'
                if not yellow_not_house1:
                    continue
                
                # If all constraints are satisfied, format the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "birthday month", "color"],
                        "rows": [
                            [house['House'], house['Name'], house['birthday month'], house['color']]
                            for house in assignment
                        ]
                    }
                }
                return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())