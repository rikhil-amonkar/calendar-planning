import os
import sys

# Function to safely redirect standard file descriptors
def setup_environment():
    # Save original file descriptors
    orig_fd = {
        'stdin': os.dup(0) if os.fstat(0) else 0,
        'stdout': os.dup(1) if os.fstat(1) else 1,
        'stderr': os.dup(2) if os.fstat(2) else 2
    }
    
    # Open null device for all streams
    devnull = open(os.devnull, 'r+')
    
    # Redirect standard file descriptors to /dev/null
    for fd in [0, 1, 2]:
        try:
            os.dup2(devnull.fileno(), fd)
        except OSError:
            pass
    
    return orig_fd, devnull

# Function to restore original file descriptors
def restore_environment(orig_fd, devnull):
    # Close null device
    if devnull:
        try:
            devnull.close()
        except:
            pass
    
    # Restore original file descriptors
    for fd, orig in orig_fd.items():
        try:
            fd_num = {'stdin': 0, 'stdout': 1, 'stderr': 2}[fd]
            os.dup2(orig, fd_num)
            os.close(orig)
        except:
            pass

# Main solving function
def solve():
    orig_fd, devnull = None, None
    try:
        # Create safe environment
        orig_fd, devnull = setup_environment()
        
        # Import Z3 after environment setup
        from z3 import Int, Solver, sat
        
        # Create solver and variables
        s = Solver()
        x = Int('x')
        y = Int('y')
        z = Int('z')
        
        # Add constraints
        s.add(x + y + z == 10)
        s.add(x - y == 2)
        
        # Solve and extract solution
        if s.check() == sat:
            m = s.model()
            return (
                m.eval(x, model_completion=True).as_long(),
                m.eval(y, model_completion=True).as_long(),
                m.eval(z, model_completion=True).as_long()
            )
        return (None, None, None)
    
    except Exception as e:
        return (f"Error: {str(e)}", None, None)
    
    finally:
        # Restore environment regardless of success/failure
        if orig_fd:
            restore_environment(orig_fd, devnull)

# Main execution
if __name__ == "__main__":
    try:
        # Get solution
        x, y, z = solve()
        
        # Prepare output
        output = ""
        if x is not None and y is not None and z is not None:
            if isinstance(x, int) and isinstance(y, int) and isinstance(z, int):
                output = f"Solution: x = {x}, y = {y}, z = {z}"
            else:
                output = str(x)  # Error message
        else:
            output = "No solution found"
        
        # Write output directly to stdout file descriptor
        os.write(1, f"{output}\n".encode())
    
    except Exception as e:
        # Fallback error handling
        os.write(2, f"Critical error: {str(e)}\n".encode())