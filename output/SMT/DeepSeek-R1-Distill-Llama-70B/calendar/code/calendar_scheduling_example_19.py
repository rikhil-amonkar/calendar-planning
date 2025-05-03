from z3 import *

# Define the blocked intervals for each person in minutes
stephen_blocked = [
    (600, 630),   # 10:00-10:30
    (780, 810),   # 13:00-13:30
    (870, 900),   # 14:30-15:00
    (960, 990)    # 16:00-16:30
]

edward_blocked = [
    (540, 570),   # 9:00-9:30
    (600, 630),   # 10:00-10:30
    (810, 870),   # 13:30-14:30
    (900, 960)    # 15:00-16:00
]

angela_blocked = [
    (540, 690),   # 9:00-11:30
    (750, 780),   # 12:30-13:00
    (810, 930),   # 13:30-15:30
    (960, 1020)   # 16:00-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
stephen_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in stephen_blocked]
edward_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in edward_blocked]
angela_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in angela_blocked]

# Combine all constraints
constraints = stephen_constraints + edward_constraints + angela_constraints

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