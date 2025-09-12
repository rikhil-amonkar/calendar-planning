import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define houses
    houses = [0, 1, 2, 3]  # 0-indexed
    
    # Define attributes
    names = ['Alice', 'Arnold', 'Peter', 'Eric']
    hair_colors = ['black', 'blonde', 'brown', 'red']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in range(4)]
    hair_vars = [Int(f'hair_{i}') for i in range(4)]
    
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
    # Eric is directly left of blonde hair, so Eric cannot be in the last house
    # and the person to his right must have blonde hair
    for i in range(3):  # Houses 0,1,2 can have Eric (right up to house 3)
        solver.add(Implies(name_vars[i] == eric_index, 
                          And(hair_vars[i+1] == blonde_index, 
                              hair_vars[i] != blonde_index)))  # Eric doesn't have blonde hair
    
    # Clue 2: Alice and Arnold are next to each other
    alice_index = names.index('Alice')
    arnold_index = names.index('Arnold')
    adjacent_constraints = []
    for i in range(3):  # Check adjacent pairs (0-1, 1-2, 2-3)
        adjacent_constraints.append(
            And(name_vars[i] == alice_index, name_vars[i+1] == arnold_index)
        )
        adjacent_constraints.append(
            And(name_vars[i] == arnold_index, name_vars[i+1] == alice_index)
        )
    solver.add(Or(adjacent_constraints))
    
    # Clue 3: Eric is the person who has brown hair
    brown_index = hair_colors.index('brown')
    for i in range(4):
        solver.add(Implies(name_vars[i] == eric_index, hair_vars[i] == brown_index))
    
    # Clue 4: The person who has black hair is not in the first house
    black_index = hair_colors.index('black')
    solver.add(hair_vars[0] != black_index)
    
    # Clue 5: Alice is in the first house
    solver.add(name_vars[0] == alice_index)
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare solution data
        rows = []
        for house in range(4):
            name_idx = model.evaluate(name_vars[house]).as_long()
            hair_idx = model.evaluate(hair_vars[house]).as_long()
            
            rows.append([
                str(house + 1),  # Display as 1-indexed
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