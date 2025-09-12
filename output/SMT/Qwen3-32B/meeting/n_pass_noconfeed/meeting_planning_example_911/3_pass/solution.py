from z3 import *

# Initialize the solver
s = Solver()

# Assuming friend_vars is a list of 10 integer variables
friend_vars = [Int(f'friend_{i}') for i in range(10)]

# Add constraints to ensure consecutive variables are different
for i in range(9):  # Check only up to the 9th position to avoid index out of range
    s.add(friend_vars[i] != friend_vars[i + 1])

# Optionally check if the constraints are satisfiable
print(s.check())