from z3 import *
import json

# Define the variables
house1_name = String('house1_name')
house1_vacation = String('house1_vacation')
house2_name = String('house2_name')
house2_vacation = String('house2_vacation')

# Create a solver instance
solver = Solver()

# Add constraints for unique names and vacations
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_vacation, house2_vacation))

# Add constraints for the possible values of names and vacations
names = ['Arnold', 'Eric']
vacations = ['beach', 'mountain']

solver.add(Or(house1_name == 'Arnold', house1_name == 'Eric'))
solver.add(Or(house1_vacation == 'beach', house1_vacation == 'mountain'))
solver.add(Or(house2_name == 'Arnold', house2_name == 'Eric'))
solver.add(Or(house2_vacation == 'beach', house2_vacation == 'mountain'))

# Add the clue constraint: Arnold is somewhere to the right of the person who loves beach vacations.
solver.add(Implies(house1_vacation == 'beach', house2_name == 'Arnold'))
solver.add(Implies(house2_vacation == 'beach', False))  # Arnold cannot be in house 1 if house 2 loves beach

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_vacation].as_string()],
                ["2", model[house2_name].as_string(), model[house2_vacation].as_string()]
            ]
        }
    }
    print(json.dumps(solution, indent=4))
else:
    print("No solution found")