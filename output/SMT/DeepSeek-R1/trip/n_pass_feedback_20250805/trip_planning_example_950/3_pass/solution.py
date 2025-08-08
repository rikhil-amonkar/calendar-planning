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
        
        # Extract values as fractions and convert to floats
        x_val = float(m[x].numerator_as_long()) / float(m[x].denominator_as_long())
        y_val = float(m[y].numerator_as_long()) / float(m[y].denominator_as_long())
        z_val = float(m[z].numerator_as_long()) / float(m[z].denominator_as_long())
        
        # Format to 6 decimal places
        print(f"{x_val:.6f},{y_val:.6f},{z_val:.6f}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()