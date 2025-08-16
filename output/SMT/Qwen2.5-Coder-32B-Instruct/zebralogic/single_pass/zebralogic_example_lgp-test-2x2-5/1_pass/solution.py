from z3 import *

# Create the solver instance
solver = Solver()

# Define variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_style = String('house1_style')
house2_style = String('house2_style')

# Define the domain of possible values
names = ['Eric', 'Arnold']
styles = ['victorian', 'colonial']

# Add constraints for names and styles
solver.add(house1_name == 'Eric')  # Eric is in the first house
solver.add(Or(house2_name == 'Arnold'))  # The second house must be occupied by Arnold

solver.add(Or(house1_style == 'victorian', house1_style == 'colonial'))
solver.add(Or(house2_style == 'victorian', house2_style == 'colonial'))

# Ensure each house has a unique style
solver.add(house1_style != house2_style)

# Ensure the person in the Victorian house is to the left of the person in the Colonial house
solver.add(Implies(house1_style == 'victorian', house2_style == 'colonial'))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_style].as_string()],
                ["2", model[house2_name].as_string(), model[house2_style].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")