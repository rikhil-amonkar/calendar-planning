from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each attribute of each person
names = ['Arnold', 'Eric']
months = ['april', 'sept']
mothers = ['Aniya', 'Holly']

# Create symbolic variables
house1_name = String('house1_name')
house1_month = String('house1_month')
house1_mother = String('house1_mother')
house2_name = String('house2_name')
house2_month = String('house2_month')
house2_mother = String('house2_mother')

# Add constraints for names, months, and mothers being unique
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_month, house2_month))
solver.add(Distinct(house1_mother, house2_mother))

# Add constraints based on the clues
# Clue 1: Eric is somewhere to the left of The person whose mother's name is Holly.
solver.add(Or(And(house1_name == 'Eric', house2_mother == 'Holly'),
             And(house1_name != 'Eric', house1_mother == 'Holly')))

# Clue 2: The person whose birthday is in April is in the first house.
solver.add(house1_month == 'april')

# Add constraints for possible values
solver.add(Or(house1_name == 'Arnold', house1_name == 'Eric'))
solver.add(Or(house1_month == 'april', house1_month == 'sept'))
solver.add(Or(house1_mother == 'Aniya', house1_mother == 'Holly'))
solver.add(Or(house2_name == 'Arnold', house2_name == 'Eric'))
solver.add(Or(house2_month == 'april', house2_month == 'sept'))
solver.add(Or(house2_mother == 'Aniya', house2_mother == 'Holly'))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_month].as_string(), model[house1_mother].as_string()],
                ["2", model[house2_name].as_string(), model[house2_month].as_string(), model[house2_mother].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")