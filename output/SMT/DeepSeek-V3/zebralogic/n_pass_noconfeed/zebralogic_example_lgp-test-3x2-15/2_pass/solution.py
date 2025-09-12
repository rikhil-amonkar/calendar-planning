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
    
    # Find the positions of Peter and Eric
    peter_pos = Int('peter_pos')
    eric_pos = Int('eric_pos')
    
    # Constrain the positions
    for i in houses:
        solver.add(Implies(name_vars[i-1] == peter_idx, peter_pos == i))
        solver.add(Implies(name_vars[i-1] == eric_idx, eric_pos == i))
    
    # Peter must be to the right of Eric
    solver.add(peter_pos > eric_pos)
    
    # Clue 2: The person who is short is in the first house
    short_idx = heights.index('short')
    solver.add(height_vars[0] == short_idx)
    
    # Clue 3: There is one house between the person who is short and the person who is very short
    very_short_idx = heights.index('very short')
    # Since short is in house 1 (from clue 2), very short must be in house 3
    solver.add(height_vars[2] == very_short_idx)
    
    # Clue 4: Arnold and the person who is very short are next to each other
    arnold_idx = names.index('Arnold')
    # Since very short is in house 3 (from clue 3), Arnold must be in house 2
    solver.add(name_vars[1] == arnold_idx)
    
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