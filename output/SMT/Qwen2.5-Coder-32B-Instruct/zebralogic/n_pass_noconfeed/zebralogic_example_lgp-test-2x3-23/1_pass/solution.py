from z3 import *
import json

# Define the variables
house1_name = String('house1_name')
house1_children = String('house1_children')
house1_food = String('house1_food')

house2_name = String('house2_name')
house2_children = String('house2_children')
house2_food = String('house2_food')

# Create the solver
solver = Solver()

# Define the domains
names = ['Eric', 'Arnold']
children = ['Bella', 'Fred']
foods = ['grilled cheese', 'pizza']

# Add domain constraints
solver.add(Or(house1_name == 'Eric', house1_name == 'Arnold'))
solver.add(Or(house1_children == 'Bella', house1_children == 'Fred'))
solver.add(Or(house1_food == 'grilled cheese', house1_food == 'pizza'))

solver.add(Or(house2_name == 'Eric', house2_name == 'Arnold'))
solver.add(Or(house2_children == 'Bella', house2_children == 'Fred'))
solver.add(Or(house2_food == 'grilled cheese', house2_food == 'pizza'))

# Add unique constraints
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_children, house2_children))
solver.add(Distinct(house1_food, house2_food))

# Add clue constraints
# Clue 1: The person who is a pizza lover is Arnold.
solver.add(Implies(house1_food == 'pizza', house1_name == 'Arnold'))
solver.add(Implies(house2_food == 'pizza', house2_name == 'Arnold'))

# Clue 2: The person who loves eating grilled cheese is directly left of the person's child is named Fred.
solver.add(Implies(house1_food == 'grilled cheese', And(house2_children == 'Fred', house1_name != 'Arnold')))
solver.add(Implies(house2_food == 'grilled cheese', False))  # This ensures that grilled cheese cannot be in house 2

# Solve the puzzle
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Children", "Food"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_children].as_string(), model[house1_food].as_string()],
                ["2", model[house2_name].as_string(), model[house2_children].as_string(), model[house2_food].as_string()]
            ]
        }
    }
    print(json.dumps(solution, indent=4))
else:
    print("No solution found")