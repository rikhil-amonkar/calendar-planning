import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define houses
    houses = [1, 2, 3]
    
    # Define attributes
    names = ['Arnold', 'Peter', 'Eric']
    heights = ['short', 'average', 'very short']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in houses]
    height_vars = [Int(f'height_{i}') for i in houses]
    
    # Constraint: All names are unique and assigned to exactly one house
    solver.add(Distinct(name_vars))
    for i in range(len(houses)):
        solver.add(name_vars[i] >= 0, name_vars[i] < len(names))
    
    # Constraint: All heights are unique and assigned to exactly one house
    solver.add(Distinct(height_vars))
    for i in range(len(houses)):
        solver.add(height_vars[i] >= 0, height_vars[i] < len(heights))
    
    # Clue 1: Peter is somewhere to the right of Eric
    peter_idx = names.index('Peter')
    eric_idx = names.index('Eric')
    for i in houses:
        for j in houses:
            if j <= i:
                solver.add(Not(And(name_vars[i-1] == peter_idx, name_vars[j-1] == eric_idx)))
    
    # Clue 2: The person who is short is in the first house
    short_idx = heights.index('short')
    solver.add(height_vars[0] == short_idx)
    
    # Clue 3: There is one house between the person who is short and the person who is very short
    very_short_idx = heights.index('very short')
    solver.add(Or(
        And(height_vars[0] == short_idx, height_vars[2] == very_short_idx),
        And(height_vars[2] == short_idx, height_vars[0] == very_short_idx)
    ))
    
    # Clue 4: Arnold and the person who is very short are next to each other
    arnold_idx = names.index('Arnold')
    for i in houses:
        if i == 1:  # First house, only check right neighbor
            solver.add(Implies(name_vars[0] == arnold_idx, height_vars[1] == very_short_idx))
            solver.add(Implies(height_vars[0] == very_short_idx, name_vars[1] == arnold_idx))
        elif i == 3:  # Last house, only check left neighbor
            solver.add(Implies(name_vars[2] == arnold_idx, height_vars[1] == very_short_idx))
            solver.add(Implies(height_vars[2] == very_short_idx, name_vars[1] == arnold_idx))
        else:  # Middle house, check both neighbors
            solver.add(Implies(name_vars[1] == arnold_idx, 
                              Or(height_vars[0] == very_short_idx, height_vars[2] == very_short_idx)))
            solver.add(Implies(height_vars[1] == very_short_idx, 
                              Or(name_vars[0] == arnold_idx, name_vars[2] == arnold_idx)))
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Extract solution
        solution = []
        for i in houses:
            house_num = str(i)
            name_idx = model.evaluate(name_vars[i-1]).as_long()
            height_idx = model.evaluate(height_vars[i-1]).as_long()
            
            name_val = names[name_idx]
            height_val = heights[height_idx]
            
            solution.append([house_num, name_val, height_val])
        
        # Format output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()