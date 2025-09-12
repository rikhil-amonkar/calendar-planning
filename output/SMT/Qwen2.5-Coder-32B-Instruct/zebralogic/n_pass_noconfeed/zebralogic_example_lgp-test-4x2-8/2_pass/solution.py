from z3 import *
import json

# Define the variables
houses = [Int(f'house_{i}') for i in range(1, 5)]
names = ['Peter', 'Arnold', 'Alice', 'Eric']
colors = ['yellow', 'green', 'red', 'white']

# Create a solver instance
solver = Solver()

# Define the domains for each variable
for house in houses:
    solver.add(house >= 1)
    solver.add(house <= 4)

# Each house is occupied by a different person
name_vars = {name: Int(name) for name in names}
color_vars = {color: Int(color) for color in colors}

# Add constraints for unique occupancy
solver.add(Distinct([name_vars[name] for name in names]))
solver.add(Distinct([color_vars[color] for color in colors]))

# Clue 1: The person whose favorite color is green is in the third house.
solver.add(color_vars['green'] == 3)

# Clue 2: Peter is in the first house.
solver.add(name_vars['Peter'] == 1)

# Clue 3: There is one house between the person whose favorite color is red and the person who loves yellow.
solver.add(Abs(color_vars['red'] - color_vars['yellow']) == 2)

# Clue 4: Arnold is directly left of Eric.
solver.add(name_vars['Arnold'] + 1 == name_vars['Eric'])

# Clue 5: Eric is the person who loves yellow.
solver.add(name_vars['Eric'] == color_vars['yellow'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": []
        }
    }
    
    house_to_name = {model.evaluate(name_vars[name]).as_long(): name for name in names}
    house_to_color = {model.evaluate(color_vars[color]).as_long(): color for color in colors}
    
    for house in range(1, 5):
        name = house_to_name.get(house, "Unknown")
        color = house_to_color.get(house, "Unknown")
        solution["solution"]["rows"].append([str(house), name, color])
    
    # Print the solution as JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")