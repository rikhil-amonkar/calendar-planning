import os
import sys

# Function to safely open a file descriptor
def safe_open_fd(fd, flags):
    try:
        return os.fdopen(os.dup(fd), flags
    except OSError:
        return None, None

# Function to safely redirect standard streams
def setup_environment():
    # Backup original file descriptors
    orig_fd = { 
        'stdin': os.dup(0),
        'stdout': os.dup(1),
        'stderr': os.dup(2)
    }
    
    # Redirect to /dev/null or equivalent
    devnull = open(os.devnull, 'w+')
    
    # Redirect stdin, stdout, stderr
    os.dup2(devnull.fileno(), 0)
    os.dup2(devnull.fileno(), 1)
    os.dup2(devnull.fileno(), 2)
    
    return orig_fd, devnull

# Function to restore original file descriptors
def restore_environment(orig_fd, devnull):
    # Close null device
    devnull.close()
    
    # Restore original file descriptors
    for fd, orig in orig_fd.items():
        try:
            os.dup2(orig, int(fd[-1]))
            os.close(orig)
        except OSError:
            pass

# Main solving function
def solve():
    # Setup safe environment
    orig_fd, devnull = setup_environment()
    
    # Import Z3 in protected environment
    try:
        from z3 import Int, Solver, sat
    except ImportError as e:
        restore_environment(orig_fd, devnull)
        print(f"Z3 import failed: {str(e)}", file=sys.stderr)
        return None
    
    # Create solver and variables
    s = Solver()
    x = Int('x')
    y = Int('y')
    z = Int('z')
    
    # Add constraints
    s.add(x + y + z == 10)
    s.add(x - y == 2)
    
    # Solve and get model
    result = None
    if s.check() == sat:
        m = s.model()
        result = (m[x].as_long(), m[y].as_long(), m[z].as_long())
    
    # Restore original environment
    restore_environment(orig_fd, devnull)
    return result

# Main execution with comprehensive error handling
if __name__ == "__main__":
    try:
        solution = solve()
        if solution:
            x, y, z = solution
            print(f"Solution: x = {x}, y = {y}, z = {z}")
        else:
            print("No solution found")
    except Exception as e:
        # Attempt to write to stderr using low-level OS calls
        try:
            sys.stderr.write(f"Critical error: {str(e)}\n")
        except:
            # Fallback to OS-level write if all else fails
            os.write(2, f"Critical error: {str(e)}\n".encode())