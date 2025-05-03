from z3 import *

# Define the blocked intervals for Kevin in minutes
kevin_blocked = [
    (540, 600),   # 9:00-10:00
    (630, 690),   # 10:30-11:30
    (720, 930),   # 12:00-15:30
    (990, 1020)   # 16:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for Kevin's blocked times
kevin_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in kevin_blocked]

# Combine all constraints
constraints = kevin_constraints

# Add the constraints for the valid time range
constraints.append(540 <= t)
constraints.append(t <= 960)

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start_time = model[t].as_long()
    hours = start_time // 60
    minutes = start_time % 60
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No solution found")