from z3 import *

# Create solver
solver = Solver()

# Define indices for easier reference
water_index = 0  # Assuming water is at index 0
mountain_index = 0  # Assuming mountain is at index 0

# Create variables (assuming these were defined elsewhere)
# You'll need to replace these with your actual variable definitions
drink_vars = [Int(f'drink_{i}') for i in range(3)]
vacation_vars = [Int(f'vacation_{i}') for i in range(3)]

# Alternative clearer implementation for clue 4:
for i in range(3):
    solver.add(Implies(drink_vars[i] == water_index, vacation_vars[i] == mountain_index))
    solver.add(Implies(vacation_vars[i] == mountain_index, drink_vars[i] == water_index))