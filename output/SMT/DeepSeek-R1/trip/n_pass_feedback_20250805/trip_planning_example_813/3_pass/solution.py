from z3 import *

def main():
    # Grid size
    n = 5
    obstacles = [(0, 2), (1, 2), (2, 2), (3, 2), (4, 2),
                 (2, 0), (2, 1), (2, 3), (2, 4)]
    start = (0, 0)
    goal = (4, 4)
    
    # Try increasing plan lengths
    for T in range(8, 41, 2):  # Try T from 8 to 40 in steps of 2
        # Create state and action variables
        x = [Int('x_%d_%d' % (T, i)) for i in range(T+1)]
        y = [Int('y_%d_%d' % (T, i)) for i in range(T+1)]
        actions = [Int('a_%d_%d' % (T, i)) for i in range(T)]
        
        s = Solver()
        
        # Initial state
        s.add(x[0] == start[0])
        s.add(y[0] == start[1])
        
        # Goal state
        s.add(x[T] == goal[0])
        s.add(y[T] == goal[1])
        
        # Constraints for each time step
        for t in range(T+1):
            s.add(x[t] >= 0, x[t] < n)
            s.add(y[t] >= 0, y[t] < n)
            # Ensure no obstacles at position (x[t], y[t])
            for (ox, oy) in obstacles:
                s.add(Not(And(x[t] == ox, y[t] == oy)))
        
        # Action constraints and transitions
        for t in range(T):
            # Define action effects: 0=up, 1=down, 2=right, 3=left, 4=stay
            dx = If(actions[t] == 2, 1, If(actions[t] == 3, -1, 0))
            dy = If(actions[t] == 0, -1, If(actions[t] == 1, 1, 0))
            
            next_x = x[t] + dx
            next_y = y[t] + dy
            
            # Check if next position is valid
            valid_pos = And(0 <= next_x, next_x < n, 0 <= next_y, next_y < n)
            valid_obs = True
            for (ox, oy) in obstacles:
                valid_obs = And(valid_obs, Not(And(next_x == ox, next_y == oy)))
            valid = And(valid_pos, valid_obs)
            
            # Transition: move if valid, else stay
            s.add(x[t+1] == If(valid, next_x, x[t]))
            s.add(y[t+1] == If(valid, next_y, y[t]))
            
            # Action must be in [0, 4]
            s.add(actions[t] >= 0, actions[t] <= 4)
        
        # Check and print the solution
        if s.check() == sat:
            m = s.model()
            x_vals = [m.evaluate(x[i]).as_long() for i in range(T+1)]
            y_vals = [m.evaluate(y[i]).as_long() for i in range(T+1)]
            action_vals = [m.evaluate(actions[i]).as_long() for i in range(T)]
            
            action_names = {
                0: 'up',
                1: 'down',
                2: 'right',
                3: 'left',
                4: 'stay'
            }
            
            print(f"Found a plan with T={T}:")
            for t in range(T+1):
                print(f"Step {t}: position ({x_vals[t]}, {y_vals[t]})")
                if t < T:
                    print(f"  Action {t}: {action_names[action_vals[t]]}")
            return
    
    print("No plan found up to T=40")

if __name__ == "__main__":
    main()