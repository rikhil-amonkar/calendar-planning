import json
from z3 import *

def solve_housing_puzzle():
    # Create solver instance
    s = Solver()

    # House numbers
    houses = [1, 2, 3, 4]

    # Define variables
    names = ['Arnold', 'Peter', 'Eric', 'Alice']
    styles = ['victorian', 'ranch', 'colonial', 'craftsman']

    # Create dictionaries to hold variables
    name_vars = {house: Int(f'name_{house}') for house in houses}
    style_vars = {house: Int(f'style_{house}') for house in houses}

    # Name constraints: each name is assigned to exactly one house
    for name_idx, name in enumerate(names):
        s.add(Or([name_vars[house] == name_idx for house in houses]))
        for house1 in houses:
            for house2 in houses:
                if house1 < house2:
                    s.add(Implies(name_vars[house1] == name_idx, name_vars[house2] != name_idx))

    # Style constraints: each style is assigned to exactly one house
    for style_idx, style in enumerate(styles):
        s.add(Or([style_vars[house] == style_idx for house in houses]))
        for house1 in houses:
            for house2 in houses:
                if house1 < house2:
                    s.add(Implies(style_vars[house1] == style_idx, style_vars[house2] != style_idx))

    # Apply specific clues
    # Clue 3: Eric is in the third house
    s.add(name_vars[3] == names.index('Eric'))
    
    # Clue 4: Arnold is in the fourth house
    s.add(name_vars[4] == names.index('Arnold'))
    
    # Clue 1: Eric is in a craftsman-style house
    s.add(style_vars[3] == styles.index('craftsman'))
    
    # Clue 5: Alice is in the Victorian house
    s.add(Or([And(name_vars[house] == names.index('Alice'), style_vars[house] == styles.index('victorian')) for house in houses]))
    
    # Clue 2: ranch is directly left of victorian
    for i in range(1, 4):
        s.add(Implies(
            style_vars[i] == styles.index('ranch'),
            style_vars[i+1] == styles.index('victorian')
        ))

    # Check for solution
    if s.check() == sat:
        model = s.model()
        
        # Prepare solution
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": []
            }
        }
        
        # Collect results
        for house in sorted(houses):
            name_idx = model.evaluate(name_vars[house]).as_long()
            style_idx = model.evaluate(style_vars[house]).as_long()
            
            row = [
                str(house),
                names[name_idx],
                styles[style_idx]
            ]
            solution["solution"]["rows"].append(row)
        
        return solution
    else:
        return {"error": "No solution found"}

# Solve and print the solution
solution = solve_housing_puzzle()
print(json.dumps(solution, indent=2))