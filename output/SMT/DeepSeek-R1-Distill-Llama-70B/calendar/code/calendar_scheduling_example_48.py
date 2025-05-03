from z3 import *

# Define the blocked intervals for each person in minutes
janet_blocked = [
    (570, 630),   # 9:30-10:30
    (750, 780),   # 12:30-13:00
    (840, 870)    # 14:00-14:30
]

cynthia_blocked = [
    (570, 600),   # 9:30-10:00
    (660, 690),   # 11:00-11:30
    (750, 870),   # 12:30-14:30
    (960, 1020)   # 16:00-17:00
]

# Create the variable for the start time, considering Cynthia's preference
t = Int('t')

# Create constraints for each person's blocked times
janet_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in janet_blocked]
cynthia_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in cynthia_blocked]

# Combine all constraints
constraints = janet_constraints + cynthia_constraints

# Add the constraints for the valid time range, considering Cynthia's preference
constraints.append(810 <= t)  # Earliest start time is 13:30 (810 minutes)
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