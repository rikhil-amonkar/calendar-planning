from z3 import *
import json

# Define the variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_birthday = String('house1_birthday')
house2_birthday = String('house2_birthday')
house1_mother = String('house1_mother')
house2_mother = String('house2_mother')

# Create the solver
solver = Solver()

# Define the domains
names = ['Arnold', 'Eric']
birthdays = ['april', 'sept']
mothers = ['Aniya', 'Holly']

# Add domain constraints
solver.add(house1_name == names[0] | house1_name == names[1])
solver.add(house2_name == names[0] | house2_name == names[1])
solver.add(house1_birthday == birthdays[0] | house1_birthday == birthdays[1])
solver.add(house2_birthday == birthdays[0] | house2_birthday == birthdays[1])
solver.add(house1_mother == mothers[0] | house1_mother == mothers[1])
solver.add(house2_mother == mothers[0] | house2_mother == mothers[1])

# Ensure uniqueness
solver.add(house1_name != house2_name)
solver.add(house1_birthday != house2_birthday)
solver.add(house1_mother != house2_mother)

# Add clue constraints
# Clue 1: Eric is somewhere to the left of The person whose mother's name is Holly.
solver.add(Or(And(house1_name == 'Eric', house2_mother == 'Holly'), And(house1_name != 'Eric', house2_name == 'Eric')))

# Clue 2: The person whose birthday is in April is in the first house.
solver.add(house1_birthday == 'april')

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_birthday].as_string(), model[house1_mother].as_string()],
                ["2", model[house2_name].as_string(), model[house2_birthday].as_string(), model[house2_mother].as_string()]
            ]
        }
    }
    print(json.dumps(solution))
else:
    print("No solution found")