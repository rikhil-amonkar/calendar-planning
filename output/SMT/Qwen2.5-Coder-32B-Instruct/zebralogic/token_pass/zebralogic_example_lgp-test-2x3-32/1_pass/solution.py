from z3 import *

# Define variables
house1_name = String('house1_name')
house1_birthday = String('house1_birthday')
house1_color = String('house1_color')

house2_name = String('house2_name')
house2_birthday = String('house2_birthday')
house2_color = String('house2_color')

# Create solver instance
solver = Solver()

# Add constraints based on the clues
# Clue 1: Eric is the person who loves yellow
solver.add(house2_name == 'Eric')
solver.add(house2_color == 'yellow')

# Clue 2: The person whose birthday is in April is in the first house
solver.add(house1_birthday == 'april')

# Clue 3: The person who loves yellow is not in the first house
solver.add(house1_color != 'yellow')

# Each person has a unique name
solver.add(Distinct(house1_name, house2_name))
solver.add(Or(house1_name == 'Arnold', house1_name == 'Eric'))
solver.add(Or(house2_name == 'Arnold', house2_name == 'Eric'))

# Each person has a unique birthday month
solver.add(Distinct(house1_birthday, house2_birthday))
solver.add(Or(house1_birthday == 'april', house1_birthday == 'sept'))
solver.add(Or(house2_birthday == 'april', house2_birthday == 'sept'))

# Each person has a unique favorite color
solver.add(Distinct(house1_color, house2_color))
solver.add(Or(house1_color == 'yellow', house1_color == 'red'))
solver.add(Or(house2_color == 'yellow', house2_color == 'red'))

# Check if the constraints are satisfiable
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
    print(solution)
else:
    print("No solution found")