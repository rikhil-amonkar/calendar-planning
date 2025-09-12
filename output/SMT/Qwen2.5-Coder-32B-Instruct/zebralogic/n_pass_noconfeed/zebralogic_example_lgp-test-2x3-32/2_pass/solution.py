from z3 import *
import json

# Define the variables
house1_name = String('house1_name')
house1_birthday = String('house1_birthday')
house1_color = String('house1_color')

house2_name = String('house2_name')
house2_birthday = String('house2_birthday')
house2_color = String('house2_color')

# Define the domains
names = ['Eric', 'Arnold']
birthdays = ['sept', 'april']
colors = ['yellow', 'red']

# Create the solver
solver = Solver()

# Add domain constraints
solver.add(Or(house1_name == 'Eric', house1_name == 'Arnold'))
solver.add(Or(house1_birthday == 'sept', house1_birthday == 'april'))
solver.add(Or(house1_color == 'yellow', house1_color == 'red'))

solver.add(Or(house2_name == 'Eric', house2_name == 'Arnold'))
solver.add(Or(house2_birthday == 'sept', house2_birthday == 'april'))
solver.add(Or(house2_color == 'yellow', house2_color == 'red'))

# Add uniqueness constraints
solver.add(house1_name != house2_name)
solver.add(house1_birthday != house2_birthday)
solver.add(house1_color != house2_color)

# Add clue constraints
# Clue 1: Eric is the person who loves yellow.
solver.add(Implies(house1_color == 'yellow', house1_name == 'Eric'))
solver.add(Implies(house2_color == 'yellow', house2_name == 'Eric'))

# Clue 2: The person whose birthday is in April is in the first house.
solver.add(house1_birthday == 'april')

# Clue 3: The person who loves yellow is not in the first house.
solver.add(house1_color != 'yellow')

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_birthday].as_string(), model[house1_color].as_string()],
                ["2", model[house2_name].as_string(), model[house2_birthday].as_string(), model[house2_color].as_string()]
            ]
        }
    }
    print(json.dumps(solution))
else:
    print("No solution found")