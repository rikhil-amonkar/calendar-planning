from z3 import *

# Initialize the solver
s = Solver()

# Define 10 integer variables
friend_vars = [Int(f'friend_{i}') for i in range(10)]

# Ensure all variables are distinct
s.add(Distinct(friend_vars))

# Constrain each variable to be between 1 and 10 (inclusive)
for var in friend_vars:
    s.add(And(1 <= var, var <= 10))

# Check if the constraints are satisfiable
result = s.check()

# If a solution exists, print it
if result == sat:
    model = s.model()
    print("Valid plan found:")
    for i, var in enumerate(friend_vars):
        print(f"Friend {i}: {model[var]}")
else:
    print("No valid plan found.")