from z3 import *

# Define integer variables
x = Int('x')
y = Int('y')

# Create a solver instance
s = Solver()

# Add constraints: 3x - 4y = 10 and |x - y| = 2
s.add(3*x - 4*y == 10)
s.add(Or(x - y == 2, x - y == -2))

# Check for a solution
if s.check() == sat:
    m = s.model()
    print(f"x = {m[x]}, y = {m[y]}")
else:
    print("No solution found")