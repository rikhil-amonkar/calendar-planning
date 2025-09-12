from z3 import *

# Step 1: Initialize the solver
solver = Solver()

# Step 2: Define 5 integer variables for the order (order_0 to order_4)
order = [Int(f'order_{i}') for i in range(5)]

# Step 3: Add constraints
# Each variable must be between 0 and 4 inclusive
solver.add([And(0 <= order[i], order[i] <= 4) for i in range(5)])

# All variables must be distinct (i.e., a permutation of 0 to 4)
solver.add(Distinct(order))

# Optional: Solve and print the model
if solver.check() == sat:
    model = solver.model()
    print(model)
else:
    print("No solution found.")