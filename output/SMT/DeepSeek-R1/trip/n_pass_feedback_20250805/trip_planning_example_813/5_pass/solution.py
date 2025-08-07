from z3 import *

def main():
    n = 5
    obstacles = [(0, 2), (1, 2), (2, 2), (3, 2), (4, 2),
                 (2, 0), (2, 1), (2, 3), (2, 4)]
    start = (0, 0)
    goal = (4, 4)
    
    # Try increasing plan lengths
    for T in range(8, 41):
        # State variables for each timestep
        x = [Int(f'x_{T}_{i}') for i in range(T+1)]
        y = [Int(f'y_{T}_{i}') for i in range(T+1)]
        # Action variables (0=up, 1=down, 2=right, 3=left, 4=stay)
        actions = [Int(f'a_{T}_{i}') for i in range(T)]
        
        s = Solver()
        
        # Initial position
        s.add(x[0] == start[0])
        s.add(y[0] == start[1])
        
        # Goal position
        s.add(x[T] == goal[0])
        s.add(y[T] == goal[1])
        
        # State constraints for all timesteps
        for t in range(T+1):
            # Grid boundaries
            s.add(x[t] >= 0, x[t] < n)
            s.add(y[t] >= 0, y[t] < n)
            # Obstacle avoidance
            for obs in obstacles:
                s.add(Not(And(x[t] == obs[0], y[t] == obs[1])))
        
        # Movement constraints between timesteps
        for t in range(T):
            # Action effects
            dx = If(actions[t] == 2, 1, If(actions[t] == 3, -1, 0))  # right/left
            dy = If(actions[t] == 0, -1, If(actions[t] == 1, 1, 0))   # up/down
            
            # Next position based on action
            next_x = x[t] + dx
            next_y = y[t] + dy
            
            # Only allow actions that result in valid positions
            s.add(x[t+1] == next_x)
            s.add(y[t+1] == next_y)
            
            # Action must be valid (0-4)
            s.add(actions[t] >= 0, actions[t] <= 4)
        
        # Check for solution
        if s.check() == sat:
            m = s.model()
            # Extract solution values
            x_vals = [m.evaluate(x[i]).as_long() for i in range(T+1)]
            y_vals = [m.evaluate(y[i]).as_long() for i in range(T+1)]
            action_vals = [m.evaluate(actions[i]).as_long() for i in range(T)]
            
            # Print the plan
            action_names = {
                0: 'up',
                1: 'down',
                2: 'right',
                3: 'left',
                4: 'stay'
            }
            print(f"Found plan with T={T}:")
            for t in range(T+1):
                print(f"Step {t}: position ({x_vals[t]}, {y_vals[t]})")
                if t < T:
                    print(f"  Action {t}: {action_names[action_vals[t]]}")
            return
    
    print("No plan found up to T=40")

if __name__ == "__main__":
    main()