from z3 import *

# Define the blocked intervals for each person in minutes
teresa_blocked = [
    (540, 600),   # 9:00-10:00
    (780, 810),   # 13:00-13:30
    (840, 870),   # 14:00-14:30
    (900, 930),   # 15:00-15:30
    (990, 1020)   # 16:30-17:00
]

kathleen_blocked = [
    (540, 570),   # 9:00-9:30
    (750, 780),   # 12:30-13:00
    (810, 840),   # 13:30-14:00
    (900, 930)    # 15:00-15:30
]

patricia_blocked = [
    (540, 630),   # 9:00-10:30
    (690, 720),   # 11:30-12:00
    (780, 810),   # 13:00-13:30
    (840, 870),   # 14:00-14:30
    (930, 960),   # 15:30-16:00
    (990, 1020)   # 16:30-17:00
]

# Create the variable for the start time, considering Kathleen's preference
t = Int('t')

# Create constraints for each person's blocked times
teresa_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in teresa_blocked]
kathleen_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in kathleen_blocked]
patricia_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in patricia_blocked]

# Combine all constraints
constraints = teresa_constraints + kathleen_constraints + patricia_constraints

# Add the constraints for the valid time range, considering Kathleen's preference
constraints.append(540 <= t)  # Earliest start time is 9:00 (540 minutes)
constraints.append(t <= 870)  # Latest start time is 14:30 (870 minutes)

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