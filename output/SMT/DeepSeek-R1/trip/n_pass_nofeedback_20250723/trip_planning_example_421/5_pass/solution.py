from z3 import *

def main():
    # Grid size and obstacles
    n = 5
    obstacles = [(1,1), (2,1), (3,1), (1,3), (2,3), (3,3)]
    T = 7  # Total time steps (0 to 7 inclusive, so 8 steps)
    
    # Create Z3 variables for positions of R1 and R2 for each time step
    R1x = [Int(f'R1x_{t}') for t in range(T+1)]
    R1y = [Int(f'R1y_{t}') for t in range(T+1)]
    R2x = [Int(f'R2x_{t}') for t in range(T+1)]
    R2y = [Int(f'R2y_{t}') for t in range(T+1)]
    
    s = Solver()
    
    # Initial positions
    s.add(R1x[0] == 0, R1y[0] == 0)
    s.add(R2x[0] == 0, R2y[0] == 4)
    
    # Goal positions at final time
    s.add(R1x[T] == 4, R1y[T] == 4)
    s.add(R2x[T] == 4, R2y[T] == 0)
    
    # Constraints for each time step
    for t in range(T+1):
        # Positions within grid boundaries
        s.add(And(0 <= R1x[t], R1x[t] < n, 0 <= R1y[t], R1y[t] < n))
        s.add(And(0 <= R2x[t], R2x[t] < n, 0 <= R2y[t], R2y[t] < n))
        
        # Obstacle avoidance
        s.add(Not(Or(*[And(R1x[t] == ox, R1y[t] == oy) for ox, oy in obstacles])))
        s.add(Not(Or(*[And(R2x[t] == ox, R2y[t] == oy) for ox, oy in obstacles])))
        
        # No collision at same time
        s.add(Not(And(R1x[t] == R2x[t], R1y[t] == R2y[t])))
    
    # Movement constraints and no swapping for consecutive times
    for t in range(T):
        # R1 movement: stay or move to adjacent cell
        move_R1 = Or(
            And(R1x[t+1] == R1x[t], R1y[t+1] == R1y[t]),  # stay
            And(R1x[t+1] == R1x[t] + 1, R1y[t+1] == R1y[t]),  # right
            And(R1x[t+1] == R1x[t] - 1, R1y[t+1] == R1y[t]),  # left
            And(R1x[t+1] == R1x[t], R1y[t+1] == R1y[t] + 1),  # down
            And(R1x[t+1] == R1x[t], R1y[t+1] == R1y[t] - 1)   # up
        )
        s.add(move_R1)
        
        # R2 movement: stay or move to adjacent cell
        move_R2 = Or(
            And(R2x[t+1] == R2x[t], R2y[t+1] == R2y[t]),  # stay
            And(R2x[t+1] == R2x[t] + 1, R2y[t+1] == R2y[t]),  # right
            And(R2x[t+1] == R2x[t] - 1, R2y[t+1] == R2y[t]),  # left
            And(R2x[t+1] == R2x[t], R2y[t+1] == R2y[t] + 1),  # down
            And(R2x[t+1] == R2x[t], R2y[t+1] == R2y[t] - 1)   # up
        )
        s.add(move_R2)
        
        # No swapping: not swapping positions in one time step
        s.add(Not(And(
            R1x[t] == R2x[t+1], R1y[t] == R2y[t+1],
            R2x[t] == R1x[t+1], R2y[t] == R1y[t+1]
        )))
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        for t in range(T+1):
            r1x = m.eval(R1x[t]).as_long()
            r1y = m.eval(R1y[t]).as_long()
            r2x = m.eval(R2x[t]).as_long()
            r2y = m.eval(R2y[t]).as_long()
            print(f"Time {t}: R1 at ({r1x},{r1y}), R2 at ({r2x},{r2y})")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()