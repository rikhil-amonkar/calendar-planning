from z3 import *
import json

# Define the variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_style = String('house1_style')
house2_style = String('house2_style')

# Create a solver instance
solver = Solver()

# Define the domain for each variable
names = ['Eric', 'Arnold']
styles = ['victorian', 'colonial']

# Add constraints for unique names and styles
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_style, house2_style))

# Add constraints based on the clues
solver.add(house1_name == 'Eric')
solver.add(house1_style < house2_style)  # 'victorian' comes before 'colonial' lexicographically

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
    print(json.dumps(solution))
else:
    print("No solution found")