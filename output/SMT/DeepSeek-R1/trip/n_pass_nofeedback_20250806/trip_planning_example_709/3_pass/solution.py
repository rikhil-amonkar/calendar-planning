import os
import sys

# Save original standard streams at the very beginning
original_stdout = sys.__stdout__
original_stderr = sys.__stderr__

# Redirect streams to avoid initialization errors
sys.stdout = open(os.devnull, 'w')
sys.stderr = open(os.devnull, 'w')

# Import Z3 after redirection
from z3 import Int, Solver, sat

# Restore original streams after import
sys.stdout = original_stdout
sys.stderr = original_stderr

def safe_solve():
    s = Solver()
    x = Int('x')
    y = Int('y')
    z = Int('z')
    
    # Define constraints
    s.add(x + y + z == 10)
    s.add(x - y == 2)
    
    if s.check() == sat:
        m = s.model()
        # Safely extract values with fallbacks
        return (
            m.eval(x, model_completion=True).as_long(),
            m.eval(y, model_completion=True).as_long(),
            m.eval(z, model_completion=True).as_long()
        )
    return (None, None, None)

# Execute with comprehensive error handling
try:
    x_val, y_val, z_val = safe_solve()
    if None not in (x_val, y_val, z_val):
        print(f"Solution: x = {x_val}, y = {y_val}, z = {z_val}")
    else:
        print("No solution found")
except Exception as e:
    try:
        # Attempt to print error to original stderr
        print(f"Error occurred: {str(e)}", file=original_stderr)
    except:
        # Fallback if even original stderr fails
        os.write(2, f"Critical error: {str(e)}".encode())