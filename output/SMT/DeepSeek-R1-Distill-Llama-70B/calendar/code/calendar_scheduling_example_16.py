from z3 import *

# Define the blocked intervals for each person in minutes
scott_blocked = [
    (570, 630),   # 9:30-10:30
    (810, 840),   # 13:30-14:00
    (870, 900),   # 14:30-15:00
    (930, 960),   # 15:30-16:00
    (990, 1020)   # 16:30-17:00
]

christine_blocked = [
    (540, 600),   # 9:00-10:00
    (630, 750),   # 10:30-12:30
    (780, 1020)   # 13:00-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
scott_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in scott_blocked]
christine_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in christine_blocked]

# Combine all constraints
constraints = scott_constraints + christine_constraints

# Add the constraints for the valid time range
constraints.append(540 <= t)
constraints.append(t <= 990)

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