from z3 import *

# Initialize the solver
solver = Solver()

# Example: Define variables (adjust based on your actual setup)
friends_vars = [Int(f'friend_{i}') for i in range(3)]  # Example with 3 friends
start_vars = [Int(f'start_{i}') for i in range(3)]
end_vars = [Int(f'end_{i}') for i in range(3)]

# Example constraint: If a friend is scheduled (not -1), then end time is greater than start time
for i in range(3):
    solver.add(Implies(friends_vars[i] != -1, end_vars[i] > start_vars[i]))

# Check for satisfiability
print(solver.check())
if solver.check() == sat:
    print(solver.model())