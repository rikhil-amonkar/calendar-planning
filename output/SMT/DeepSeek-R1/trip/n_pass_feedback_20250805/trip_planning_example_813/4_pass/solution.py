from z3 import *

def main():
    n = 5
    obstacles = [(0, 2), (1, 2), (2, 2), (3, 2), (4, 2),
                 (2, 0), (2, 1), (2, 3), (2, 4)]
    start = (0, 0)
    goal = (4, 4)
    
    for T in range(8, 41):
        x = [Int(f'x_{T}_{i}') for i in range(T+1)]
        y = [Int(f'y_{T}_{i}') for i in range(T+1)]
        actions = [Int(f'a_{T}_{i}') for i in range(T)]
        
        s = Solver()
        
        s.add(x[0] == start[0], y[0] == start[1])
        s.add(x[T] == goal[0], y[T] == goal[1])
        
        for t in range(T+1):
            s.add(x[t] >= 0, x[t] < n)
            s.add(y[t] >= 0, y[t] < n)
            for obs in obstacles:
                s.add(Not(And(x[t] == obs[0], y[t] == obs[1])))
        
        for t in range(T):
            dx = If(actions[t] == 2, 1, If(actions[t] == 3, -1, 0))
            dy = If(actions[t] == 0, -1, If(actions[t] == 1, 1, 0))
            
            next_x = x[t] + dx
            next_y = y[t] + dy
            
            valid_pos = And(0 <= next_x, next_x < n, 0 <= next_y, next_y < n)
            valid_obs = True
            for obs in obstacles:
                valid_obs = And(valid_obs, Not(And(next_x == obs[0], next_y == obs[1])))
            valid_move = And(valid_pos, valid_obs)
            
            s.add(x[t+1] == If(valid_move, next_x, x[t]))
            s.add(y[t+1] == If(valid_move, next_y, y[t]))
            s.add(actions[t] >= 0, actions[t] <= 4)
        
        if s.check() == sat:
            m = s.model()
            x_vals = [m.evaluate(x[i]).as_long() for i in range(T+1)]
            y_vals = [m.evaluate(y[i]).as_long() for i in range(T+1)]
            action_vals = [m.evaluate(actions[i]).as_long() for i in range(T)]
            
            print(f"Found plan with T={T}:")
            for t in range(T+1):
                print(f"  Step {t}: ({x_vals[t]}, {y_vals[t]})")
            return
            
    print("No plan found up to T=40")

if __name__ == "__main__":
    main()