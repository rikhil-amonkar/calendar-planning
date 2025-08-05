from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
x = Int('x')
y = Int('y')

# Add constraints
solver.add(x + y == 10)
solver.add(x - y == 2)

# Check if the constraints can be satisfied
if solver.check() == sat:
    model = solver.model()
    print(f"x = {model[x]}, y = {model[y]}")
else:
    print("No solution found")