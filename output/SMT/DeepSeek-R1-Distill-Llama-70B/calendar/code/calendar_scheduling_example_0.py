from z3 import *

# Define the blocked intervals for each person in minutes
michelle_blocked = [(660, 720)]  # 11:00-12:00
steven_blocked = [
    (540, 570),   # 9:00-9:30
    (690, 720),   # 11:30-12:00
    (810, 840),   # 13:30-14:00
    (930, 960)    # 15:30-16:00
]
jerry_blocked = [
    (540, 570),   # 9:00-9:30
    (600, 660),   # 10:00-11:00
    (690, 750),   # 11:30-12:30
    (780, 870),   # 13:00-14:30
    (930, 960),   # 15:30-16:00
    (990, 1020)   # 16:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
michelle_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in michelle_blocked]
steven_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in steven_blocked]
jerry_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in jerry_blocked]

# Combine all constraints
constraints = michelle_constraints + steven_constraints + jerry_constraints

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