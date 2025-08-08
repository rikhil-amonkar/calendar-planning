from z3 import *

def main():
    s = Solver()
    
    # Define variables
    x = Real('x')
    y = Real('y')
    z = Real('z')
    
    # Add constraints
    s.add(x + y + z == 32)
    s.add(x - y == 2)
    s.add(2*y + 3*z == 52)
    
    # Solve and handle solution
    if s.check() == sat:
        m = s.model()
        
        # Extract values as string representations
        x_str = str(m.eval(x))
        y_str = str(m.eval(y))
        z_str = str(m.eval(z))
        
        # Convert rational strings to floats
        def to_float(s):
            if '/' in s:
                num, denom = map(float, s.split('/'))
                return num / denom
            return float(s)
        
        x_val = to_float(x_str)
        y_val = to_float(y_str)
        z_val = to_float(z_str)
        
        # Format to 6 decimal places
        print(f"{x_val:.6f},{y_val:.6f},{z_val:.6f}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()