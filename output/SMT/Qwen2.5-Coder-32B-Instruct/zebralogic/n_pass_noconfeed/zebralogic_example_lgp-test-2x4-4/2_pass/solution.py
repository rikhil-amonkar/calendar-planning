from z3 import *
import json

# Define the variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_style = String('house1_style')
house2_style = String('house2_style')
house1_height = String('house1_height')
house2_height = String('house2_height')
house1_education = String('house1_education')
house2_education = String('house2_education')

# Create a solver instance
solver = Solver()

# Define the domains
names = ['Eric', 'Arnold']
styles = ['victorian', 'colonial']
heights = ['very short', 'short']
educations = ['associate', 'high school']

# Add domain constraints
solver.add(Or(house1_name == names[0], house1_name == names[1]))
solver.add(Or(house2_name == names[0], house2_name == names[1]))
solver.add(Or(house1_style == styles[0], house1_style == styles[1]))
solver.add(Or(house2_style == styles[0], house2_style == styles[1]))
solver.add(Or(house1_height == heights[0], house1_height == heights[1]))
solver.add(Or(house2_height == heights[0], house2_height == heights[1]))
solver.add(Or(house1_education == educations[0], house1_education == educations[1]))
solver.add(Or(house2_education == educations[0], house2_education == educations[1]))

# Add uniqueness constraints
solver.add(house1_name != house2_name)
solver.add(house1_style != house2_style)
solver.add(house1_height != house2_height)
solver.add(house1_education != house2_education)

# Add clue constraints
# Clue 1: The person who is short is directly left of Eric.
solver.add(Implies(house1_height == 'short', house2_name == 'Eric'))
# Clue 2: The person residing in a Victorian house is in the first house.
solver.add(house1_style == 'victorian')
# Clue 3: The person who is short is the person with an associate's degree.
solver.add(Implies(house1_height == 'short', house1_education == 'associate'))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Height", "Education"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_style].as_string(), model[house1_height].as_string(), model[house1_education].as_string()],
                ["2", model[house2_name].as_string(), model[house2_style].as_string(), model[house2_height].as_string(), model[house2_education].as_string()]
            ]
        }
    }
    print(json.dumps(solution))
else:
    print("No solution found")