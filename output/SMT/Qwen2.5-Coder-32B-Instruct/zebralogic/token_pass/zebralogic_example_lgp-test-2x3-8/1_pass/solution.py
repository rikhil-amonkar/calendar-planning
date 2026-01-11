from z3 import *

# Define the variables
house1_name = String('house1_name')
house1_birthday = String('house1_birthday')
house1_mother = String('house1_mother')

house2_name = String('house2_name')
house2_birthday = String('house2_birthday')
house2_mother = String('house2_mother')

# Define the possible values for each variable
names = ['Arnold', 'Eric']
birthdays = ['april', 'sept']
mothers = ['Aniya', 'Holly']

# Create the solver
solver = Solver()

# Add constraints for unique values within each category
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_birthday, house2_birthday))
solver.add(Distinct(house1_mother, house2_mother))

# Add constraints for the specific values
solver.add(Or(house1_name == 'Arnold', house1_name == 'Eric'))
solver.add(Or(house2_name == 'Arnold', house2_name == 'Eric'))

solver.add(Or(house1_birthday == 'april', house1_birthday == 'sept'))
solver.add(Or(house2_birthday == 'april', house2_birthday == 'sept'))

solver.add(Or(house1_mother == 'Aniya', house1_mother == 'Holly'))
solver.add(Or(house2_mother == 'Aniya', house2_mother == 'Holly'))

# Constraint 1: Eric is somewhere to the left of the person whose mother's name is Holly.
solver.add(Implies(house1_name == 'Eric', house2_mother != 'Holly'))
solver.add(Implies(house2_name == 'Eric', house1_mother == 'Holly'))

# Constraint 2: The person whose birthday is in April is in the first house.
solver.add(house1_birthday == 'april')

# Solve the model
if solver.check() == sat:
    model = solver.model()
    house1_name_val = model[house1_name].as_string()
    house1_birthday_val = model[house1_birthday].as_string()
    house1_mother_val = model[house1_mother].as_string()
    
    house2_name_val = model[house2_name].as_string()
    house2_birthday_val = model[house2_birthday].as_string()
    house2_mother_val = model[house2_mother].as_string()
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother"],
            "rows": [
                ["1", house1_name_val, house1_birthday_val, house1_mother_val],
                ["2", house2_name_val, house2_birthday_val, house2_mother_val]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")