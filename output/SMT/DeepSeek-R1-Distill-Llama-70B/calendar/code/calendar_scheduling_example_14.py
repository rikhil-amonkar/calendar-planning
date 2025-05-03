from z3 import *

# Define the blocked intervals for each person in minutes
brandon_blocked = [
    (780, 840),   # 13:00-14:00
    (930, 960),   # 15:30-16:00
    (990, 1020)   # 16:30-17:00
]

bradley_blocked = [
    (540, 690),   # 9:00-11:30
    (720, 900),   # 12:00-15:00
    (960, 990)    # 16:00-16:30
]

# Create the variable for the start time, considering Brandon's preference
t = Int('t')

# Create constraints for each person's blocked times
brandon_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in brandon_blocked]
bradley_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in bradley_blocked]

# Combine all constraints
constraints = brandon_constraints + bradley_constraints

# Add the constraints for the valid time range, considering Brandon's preference
constraints.append(870 <= t)  # Start time must be at least 14:30 (870 minutes)
constraints.append(t <= 960)  # Latest start time is 16:00 (960 minutes)

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