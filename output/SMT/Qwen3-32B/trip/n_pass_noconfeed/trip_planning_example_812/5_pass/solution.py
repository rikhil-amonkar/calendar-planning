from z3 import *

# Initialize the Z3 solver
s = Solver()

# Declare order as an array of 7 integer variables
order = [Int(f'x{i}') for i in range(7)]

# Add constraints to ensure each value is between 0 and 6 (inclusive)
s.add(And([And(0 <= order[i], order[i] < 7) for i in range(7)]))

# Example additional constraint (optional)
# s.add(Distinct(order))  # Uncomment if values must be unique

# Check for solution
if s.check() == sat:
    model = s.model()
    print("Solution found:")
    print([model[order[i]] for i in range(7)])
else:
    print("No solution")