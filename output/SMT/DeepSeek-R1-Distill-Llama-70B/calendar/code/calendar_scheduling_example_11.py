from z3 import *

# Define the blocked intervals for each person in minutes
alexander_blocked = [
    (570, 600),   # 9:30-10:00
    (630, 660),   # 10:30-11:00
    (750, 780),   # 12:30-13:00
    (870, 900),   # 14:30-15:00
    (960, 1020)   # 16:00-17:00
]

elizabeth_blocked = [
    (540, 570),   # 9:00-9:30
    (690, 750),   # 11:30-12:30
    (780, 870)    # 13:00-14:30
]

walter_blocked = [
    (540, 870),   # 9:00-14:30
    (930, 1020)   # 15:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
alexander_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in alexander_blocked]
elizabeth_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in elizabeth_blocked]
walter_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in walter_blocked]

# Combine all constraints
constraints = alexander_constraints + elizabeth_constraints + walter_constraints

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