import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define houses
    houses = [1, 2, 3, 4]
    
    # Define attributes
    names = ['Alice', 'Arnold', 'Peter', 'Eric']
    hair_colors = ['black', 'blonde', 'brown', 'red']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in houses]
    hair_vars = [Int(f'hair_{i}') for i in houses]
    
    # Constraint: All name variables must be within valid range (0-3)
    for n in name_vars:
        solver.add(n >= 0, n < len(names))
    
    # Constraint: All hair variables must be within valid range (0-3)
    for h in hair_vars:
        solver.add(h >= 0, h < len(hair_colors))
    
    # Constraint: All names are distinct
    solver.add(Distinct(name_vars))
    
    # Constraint: All hair colors are distinct
    solver.add(Distinct(hair_vars))
    
    # Clue 1: Eric is directly left of the person who has blonde hair
    eric_index = names.index('Eric')
    blonde_index = hair_colors.index('blonde')
    for i in range(1, 4):  # Houses 2,3,4 can have Eric to their left
        solver.add(Implies(name_vars[i] == eric_index, hair_vars[i+1] == blonde_index))
    
    # Clue 2: Alice and Arnold are next to each other
    alice_index = names.index('Alice')
    arnold_index = names.index('Arnold')
    for i in range(1, 4):  # Check adjacent pairs
        solver.add(Or(
            And(name_vars[i] == alice_index, name_vars[i+1] == arnold_index),
            And(name_vars[i] == arnold_index, name_vars[i+1] == alice_index)
        ))
    
    # Clue 3: Eric is the person who has brown hair
    brown_index = hair_colors.index('brown')
    for i in houses:
        solver.add(Implies(name_vars[i] == eric_index, hair_vars[i] == brown_index))
    
    # Clue 4: The person who has black hair is not in the first house
    black_index = hair_colors.index('black')
    solver.add(hair_vars[1] != black_index)
    
    # Clue 5: Alice is in the first house
    solver.add(name_vars[1] == alice_index)
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare solution data
        rows = []
        for house in houses:
            name_idx = model.evaluate(name_vars[house]).as_long()
            hair_idx = model.evaluate(hair_vars[house]).as_long()
            
            rows.append([
                str(house),
                names[name_idx],
                hair_colors[hair_idx]
            ])
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()