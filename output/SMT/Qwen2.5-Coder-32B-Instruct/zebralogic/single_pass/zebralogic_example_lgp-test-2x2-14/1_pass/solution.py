from z3 import *

# Create the solver
solver = Solver()

# Define the variables
house_1_name = String('house_1_name')
house_2_name = String('house_2_name')
house_1_food = String('house_1_food')
house_2_food = String('house_2_food')

# Define the domain for the variables
names = ['Eric', 'Arnold']
foods = ['pizza', 'grilled cheese']

# Add constraints for names and foods
solver.add(Or(house_1_name == 'Eric', house_1_name == 'Arnold'))
solver.add(Or(house_2_name == 'Eric', house_2_name == 'Arnold'))
solver.add(Or(house_1_food == 'pizza', house_1_food == 'grilled cheese'))
solver.add(Or(house_2_food == 'pizza', house_2_food == 'grilled cheese'))

# Ensure each house has a unique name and food
solver.add(Distinct(house_1_name, house_2_name))
solver.add(Distinct(house_1_food, house_2_food))

# Add the clues as constraints
# Clue 1: The person who is a pizza lover is in the second house.
solver.add(house_2_food == 'pizza')

# Clue 2: Arnold is not in the first house.
solver.add(house_1_name != 'Arnold')

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": [
                ["1", model[house_1_name].as_string(), model[house_1_food].as_string()],
                ["2", model[house_2_name].as_string(), model[house_2_food].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")