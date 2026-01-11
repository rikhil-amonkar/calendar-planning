from z3 import *

# Create variables for the problem
house1_name = String('house1_name')
house1_style = String('house1_style')
house2_name = String('house2_name')
house2_style = String('house2_style')

# Define the domain of possible values for each variable
solver = Solver()
solver.add(Or(house1_name == 'Eric', house1_name == 'Arnold'))
solver.add(Or(house2_name == 'Eric', house2_name == 'Arnold'))
solver.add(Or(house1_style == 'victorian', house1_style == 'colonial'))
solver.add(Or(house2_style == 'victorian', house2_style == 'colonial'))

# Add constraints based on the clues
# Clue 1: The person residing in a Victorian house is somewhere to the left of the person living in a colonial-style house.
solver.add(Implies(house1_style == 'victorian', house2_style == 'colonial'))
# Clue 2: Eric is in the first house.
solver.add(house1_name == 'Eric')

# Ensure that each house has a unique person and house style
solver.add(house1_name != house2_name)
solver.add(house1_style != house2_style)

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": [
                ["1", str(model[house1_name]), str(model[house1_style])],
                ["2", str(model[house2_name]), str(model[house2_style])]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")