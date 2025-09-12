from z3 import *
import json

# Define the variables
names = ['Arnold', 'Peter', 'Eric', 'Alice']
styles = ['victorian', 'ranch', 'colonial', 'craftsman']
houses = range(1, 5)

# Create a solver instance
solver = Solver()

# Create dictionaries to map names and styles to integer variables
name_vars = {name: Int(name) for name in names}
style_vars = {style: Int(style) for style in styles}

# Add constraints for unique values
solver.add(Distinct([name_vars[name] for name in names]))
solver.add(Distinct([style_vars[style] for style in styles]))

# Add constraints based on the clues
# Clue 1: Eric is the person in a Craftsman-style house.
solver.add(name_vars['Eric'] == style_vars['craftsman'])

# Clue 2: The person in a ranch-style home is directly left of the person residing in a Victorian house.
solver.add(ForAll([Int('x')], Implies(style_vars['ranch'] == Int('x'), style_vars['victorian'] == Int('x') + 1)))

# Clue 3: Eric is in the third house.
solver.add(name_vars['Eric'] == 3)

# Clue 4: Arnold is in the fourth house.
solver.add(name_vars['Arnold'] == 4)

# Clue 5: The person residing in a Victorian house is Alice.
solver.add(style_vars['victorian'] == name_vars['Alice'])

# Ensure all names and styles are assigned to houses 1 through 4
for name in names:
    solver.add(And(name_vars[name] >= 1, name_vars[name] <= 4))

for style in styles:
    solver.add(And(style_vars[style] >= 1, style_vars[style] <= 4))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": []
        }
    }
    
    # Map house numbers to names and styles
    house_to_name = {model.evaluate(name_vars[name]).as_long(): name for name in names}
    house_to_style = {model.evaluate(style_vars[style]).as_long(): style for style in styles}
    
    # Populate the rows
    for house in houses:
        name = house_to_name[house]
        style = house_to_style[house]
        solution["solution"]["rows"].append([str(house), name, style])
    
    # Output the solution as JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")