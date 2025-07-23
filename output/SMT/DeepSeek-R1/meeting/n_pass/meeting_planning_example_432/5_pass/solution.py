from z3 import *

# Initialize solver
s = Solver()

# Define horizon
horizon = 8

# Create position variables for each time step
x = [Int(f'x_{i}') for i in range(horizon + 1)]
y = [Int(f'y_{i}') for i in range(horizon + 1)]

# Obstacles
obstacles = [(0, 3), (1, 1), (2, 3)]

# Initial position constraint
s.add(x[0] == 0, y[0] == 0)

# Goal position constraint at the last step
s.add(x[horizon] == 3, y[horizon] == 3)

# Constraints for each time step
for t in range(horizon + 1):
    # Stay within grid bounds
    s.add(x[t] >= 0, x[t] <= 3, y[t] >= 0, y[t] <= 3)
    
    # Avoid obstacles
    for (ox, oy) in obstacles:
        s.add(Not(And(x[t] == ox, y[t] == oy)))

# Movement constraints between consecutive steps
for t in range(horizon):
    # Check if robot is at goal at current step
    at_goal = And(x[t] == 3, y[t] == 3)
    
    # Define possible moves: only right or down when not at goal
    move_right = And(x[t+1] == x[t] + 1, y[t+1] == y[t], x[t] < 3)
    move_down = And(x[t+1] == x[t], y[t+1] == y[t] + 1, y[t] < 3)
    
    # If at goal, must stay; otherwise must move right or down
    s.add(If(at_goal, 
             And(x[t+1] == x[t], y[t+1] == y[t]), 
             Or(move_right, move_down)))

# Check for a solution and print the plan
if s.check() == sat:
    m = s.model()
    plan = []
    for t in range(horizon + 1):
        x_val = m.eval(x[t]).as_long()
        y_val = m.eval(y[t]).as_long()
        plan.append((x_val, y_val))
    print("Solution found! Path:")
    for t, pos in enumerate(plan):
        print(f"Step {t}: {pos}")
else:
    print("No solution found.")