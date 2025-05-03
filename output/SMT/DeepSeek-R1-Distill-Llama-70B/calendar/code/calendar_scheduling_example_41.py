from z3 import *

# Define the blocked intervals for each person in minutes
nancy_blocked = [
    (660, 750),   # 11:00-12:30
    (780, 810),   # 13:00-13:30
    (840, 900)    # 14:00-15:00
]

patricia_blocked = [
    (600, 720),   # 10:00-12:00
    (750, 780),   # 12:30-13:00
    (810, 960)    # 13:30-16:00
]

# Create the variable for the start time, considering Alan's preference
t = Int('t')

# Create constraints for each person's blocked times
nancy_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in nancy_blocked]
patricia_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in patricia_blocked]

# Combine all constraints
constraints = nancy_constraints + patricia_constraints

# Add the constraints for the valid time range, considering Alan's preference
constraints.append(870 <= t)  # Earliest start time is 14:30 (870 minutes)
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