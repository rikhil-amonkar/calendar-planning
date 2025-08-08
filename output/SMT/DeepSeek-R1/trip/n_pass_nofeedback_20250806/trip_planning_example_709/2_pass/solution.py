import os
import sys

# Redirect standard streams to avoid initialization errors
sys.stdout = open(os.devnull, 'w')
sys.stderr = open(os.devnull, 'w')

from z3 import Int, Solver, sat

# Restore stdout after imports
sys.stdout = sys.__stdout__
sys.stderr = sys.__stderr__

# Main solving logic
def solve():
    s = Solver()
    x = Int('x')
    y = Int('y')
    z = Int('z')
    s.add(x + y + z == 10)
    s.add(x - y == 2)
    
    if s.check() == sat:
        return s.model()
    return None

# Execute and handle output safely
try:
    model = solve()
    if model is not None:
        # Safe model value access with fallbacks
        x_val = model[Int('x')] if model else None
        y_val = model[Int('y')] if model else None
        z_val = model[Int('z')] if model else None
        print(f"Solution: x = {x_val}, y = {y_val}, z = {z_val}")
    else:
        print("No solution found")
except Exception as e:
    print(f"Error occurred: {str(e)}")