import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define houses
    houses = [0, 1, 2, 3]  # Use 0-based indexing for consistency
    house_numbers = [1, 2, 3, 4]  # Actual house numbers for display
    
    # Define attributes
    names = ['Peter', 'Arnold', 'Alice', 'Eric']
    colors = ['yellow', 'green', 'red', 'white']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in house_numbers]
    color_vars = [Int(f'color_{i}') for i in house_numbers]
    
    # Constraint: All names are distinct and within valid range
    solver.add(Distinct(name_vars))
    for i in house_numbers:
        solver.add(name_vars[i-1] >= 0)
        solver.add(name_vars[i-1] < len(names))
    
    # Constraint: All colors are distinct and within valid range
    solver.add(Distinct(color_vars))
    for i in house_numbers:
        solver.add(color_vars[i-1] >= 0)
        solver.add(color_vars[i-1] < len(colors))
    
    # Clue 1: The person whose favorite color is green is in the third house.
    green_index = colors.index('green')
    solver.add(color_vars[2] == green_index)  # House 3 is index 2
    
    # Clue 2: Peter is in the first house.
    peter_index = names.index('Peter')
    solver.add(name_vars[0] == peter_index)  # House 1 is index 0
    
    # Clue 3: There is one house between the person whose favorite color is red and the person who loves yellow.
    red_index = colors.index('red')
    yellow_index = colors.index('yellow')
    
    # Create all possible positions for red and yellow with one house between
    red_yellow_constraints = []
    for i in range(len(house_numbers)):
        for j in range(len(house_numbers)):
            if abs(i - j) == 2:  # Exactly one house between
                red_yellow_constraints.append(And(
                    color_vars[i] == red_index,
                    color_vars[j] == yellow_index
                ))
    solver.add(Or(red_yellow_constraints))
    
    # Clue 4: Arnold is directly left of Eric.
    arnold_index = names.index('Arnold')
    eric_index = names.index('Eric')
    
    # Arnold must be in position i and Eric in position i+1
    arnold_eric_constraints = []
    for i in range(len(house_numbers) - 1):
        arnold_eric_constraints.append(And(
            name_vars[i] == arnold_index,
            name_vars[i + 1] == eric_index
        ))
    solver.add(Or(arnold_eric_constraints))
    
    # Clue 5: Eric is the person who loves yellow.
    # This means Eric's house has yellow color
    eric_yellow_constraints = []
    for i in range(len(house_numbers)):
        eric_yellow_constraints.append(And(
            name_vars[i] == eric_index,
            color_vars[i] == yellow_index
        ))
    solver.add(Or(eric_yellow_constraints))
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare solution data
        solution_data = {
            "solution": {
                "header": ["House", "Name", "Color"],
                "rows": []
            }
        }
        
        # Extract values from model
        for i, house_num in enumerate(house_numbers):
            name_idx = model.evaluate(name_vars[i]).as_long()
            color_idx = model.evaluate(color_vars[i]).as_long()
            
            row = [
                str(house_num),
                names[name_idx],
                colors[color_idx]
            ]
            solution_data["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(solution_data, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()