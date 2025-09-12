from z3 import *
import json

# Define the variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_food = String('house1_food')
house2_food = String('house2_food')

# Create a solver instance
solver = Solver()

# Define the domain of possible values
names = ['Eric', 'Arnold']
foods = ['pizza', 'grilled cheese']

# Add constraints for unique names and foods per house
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_food, house2_food))

# Add constraints based on the clues
solver.add(house2_food == 'pizza')
solver.add(house1_name != 'Arnold')

# Add constraints for domain values
solver.add(Or(house1_name == 'Eric', house1_name == 'Arnold'))
solver.add(Or(house2_name == 'Eric', house2_name == 'Arnold'))
solver.add(Or(house1_food == 'pizza', house1_food == 'grilled cheese'))
solver.add(Or(house2_food == 'pizza', house2_food == 'grilled cheese'))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_food].as_string()],
                ["2", model[house2_name].as_string(), model[house2_food].as_string()]
            ]
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")