from z3 import *

# Define the blocked intervals for each person in minutes
debra_blocked = [
    (570, 600),   # 9:30-10:00
    (660, 690),   # 11:00-11:30
    (720, 780),   # 12:00-13:00
    (840, 870),   # 14:00-14:30
    (960, 990)    # 16:00-16:30
]

kevin_blocked = [
    (540, 720),   # 9:00-12:00
    (840, 1020)   # 14:00-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
debra_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in debra_blocked]
kevin_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in kevin_blocked]

# Combine all constraints
constraints = debra_constraints + kevin_constraints

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