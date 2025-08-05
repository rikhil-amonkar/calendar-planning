from z3 import *

# Define integer variables
x = Int('x')
y = Int('y')

# Create solver
s = Solver()

# Add constraints: 
# 1) 3x - 4y = 10 
# 2) |x - y| = 2 (implemented as two cases)
# 3) Both x and y must be positive integers
s.add(3*x - 4*y == 10)
s.add(Or(x - y == 2, x - y == -2))
s.add(x > 0, y > 0)

# Check for solution
if s.check() == sat:
    m = s.model()
    print(f"x = {m[x]}, y = {m[y]}")
else:
    print("No solution found")