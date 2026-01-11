from z3 import *

# Create variables for each attribute in each house
house1_name = String('house1_name')
house1_food = String('house1_food')
house1_mother = String('house1_mother')

house2_name = String('house2_name')
house2_food = String('house2_food')
house2_mother = String('house2_mother')

# Define the domain of possible values for each variable
names = ['Arnold', 'Eric']
foods = ['grilled cheese', 'pizza']
mothers = ['Holly', 'Aniya']

# Create the solver
solver = Solver()

# Add constraints for each house
solver.add(Or(house1_name == 'Arnold', house1_name == 'Eric'))
solver.add(Or(house1_food == 'grilled cheese', house1_food == 'pizza'))
solver.add(Or(house1_mother == 'Holly', house1_mother == 'Aniya'))

solver.add(Or(house2_name == 'Arnold', house2_name == 'Eric'))
solver.add(Or(house2_food == 'grilled cheese', house2_food == 'pizza'))
solver.add(Or(house2_mother == 'Holly', house2_mother == 'Aniya'))

# Ensure all names, foods, and mothers are unique
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_food, house2_food))
solver.add(Distinct(house1_mother, house2_mother))

# Apply Clue 1: The person who loves eating grilled cheese is directly left of the person who is a pizza lover.
solver.add(Implies(house1_food == 'grilled cheese', house2_food == 'pizza'))
solver.add(Implies(house2_food == 'grilled cheese', house1_food == 'pizza'))

# Apply Clue 2: Arnold is not in the second house.
solver.add(house2_name != 'Arnold')

# Apply Clue 3: Arnold is The person whose mother's name is Holly.
solver.add(Implies(house1_name == 'Arnold', house1_mother == 'Holly'))
solver.add(Implies(house2_name == 'Arnold', house2_mother == 'Holly'))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    house1_name_val = model[house1_name].as_string()[1:-1]  # Remove quotes
    house1_food_val = model[house1_food].as_string()[1:-1]  # Remove quotes
    house1_mother_val = model[house1_mother].as_string()[1:-1]  # Remove quotes

    house2_name_val = model[house2_name].as_string()[1:-1]  # Remove quotes
    house2_food_val = model[house2_food].as_string()[1:-1]  # Remove quotes
    house2_mother_val = model[house2_mother].as_string()[1:-1]  # Remove quotes

    solution = {
        "solution": {
            "header": ["House", "Name", "Food", "Mother"],
            "rows": [
                ["1", house1_name_val, house1_food_val, house1_mother_val],
                ["2", house2_name_val, house2_food_val, house2_mother_val]
            ]
        }
    }

    print(solution)
else:
    print("No solution found")