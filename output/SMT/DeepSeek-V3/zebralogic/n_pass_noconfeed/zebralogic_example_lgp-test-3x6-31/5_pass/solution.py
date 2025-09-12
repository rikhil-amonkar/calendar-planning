from z3 import *

# Create solver
solver = Solver()

# Define the categories and their options
drinks = ["water", "orange juice", "milk"]
vacations = ["beach", "mountain", "desert"]

# Create variables for each person (0, 1, 2)
drink_vars = [Int(f'drink_{i}') for i in range(3)]
vacation_vars = [Int(f'vacation_{i}') for i in range(3)]

# Add constraints: each variable must be between 0-2 (index of options)
for i in range(3):
    solver.add(drink_vars[i] >= 0, drink_vars[i] < 3)
    solver.add(vacation_vars[i] >= 0, vacation_vars[i] < 3)

# All drinks and vacations must be different (no repeats)
solver.add(Distinct(drink_vars))
solver.add(Distinct(vacation_vars))

# Define indices for easier reference
water_index = drinks.index("water")
mountain_index = vacations.index("mountain")

# Clue 4: The person who drank water went to the mountains
for i in range(3):
    solver.add(Implies(drink_vars[i] == water_index, vacation_vars[i] == mountain_index))
    solver.add(Implies(vacation_vars[i] == mountain_index, drink_vars[i] == water_index))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Print the results
    print("Solution found:")
    for i in range(3):
        drink = drinks[model.evaluate(drink_vars[i]).as_long()]
        vacation = vacations[model.evaluate(vacation_vars[i]).as_long()]
        print(f"Person {i}: drank {drink}, vacationed at {vacation}")
else:
    print("No solution found with the given constraints")