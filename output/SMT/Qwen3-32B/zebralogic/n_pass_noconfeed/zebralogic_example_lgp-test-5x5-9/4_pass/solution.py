from z3 import *

# Initialize the solver
s = Solver()

# Define the symbolic variables
eric_pos = Int('eric_pos')
tea = Int('tea')

# Assuming there are 6 houses, each with a drink
drink = [Int(f'drink_{i}') for i in range(6)]

# Add the constraint: If Eric is in house i (0-based), then the drink in house i+1 is tea
for i in range(4):
    s.add(Implies(eric_pos == i, drink[i + 1] == tea))

# Example: Check if the constraints are satisfiable
if s.check() == sat:
    print("Solution found:")
    print(s.model())
else:
    print("No solution found.")