from z3 import *

# Define the Z3 solver
solver = Solver()

# Example variables for scheduling
x1 = Int('x1')  # Represents a time slot for task 1
x2 = Int('x2')  # Represents a time slot for task 2

# Add constraints
solver.add(x1 >= 0, x1 <= 10)  # Task 1 must be scheduled between 0 and 10
solver.add(x2 >= 0, x2 <= 10)  # Task 2 must be scheduled between 0 and 10
solver.add(x1 != x2)            # Task 1 and Task 2 cannot overlap

# Check if the constraints can be satisfied
if solver.check() == sat:
    model = solver.model()
    print(f'Task 1 is scheduled at: {model[x1]}')
    print(f'Task 2 is scheduled at: {model[x2]}')
else:
    print("No solution found.")