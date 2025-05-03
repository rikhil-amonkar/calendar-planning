from z3 import *

# Define the blocked intervals for each person in minutes
billy_blocked = [
    (690, 720),   # 11:30-12:00
    (780, 900),   # 13:00-15:00
    (960, 990)    # 16:00-16:30
]

maria_blocked = [
    (540, 570),   # 9:00-9:30
    (600, 630),   # 10:00-10:30
    (780, 810),   # 13:00-13:30
    (840, 870)    # 14:00-14:30
]

william_blocked = [
    (570, 600),   # 9:30-10:00
    (720, 750),   # 12:00-12:30
    (810, 900),   # 13:30-15:00
    (930, 1020)   # 15:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
billy_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in billy_blocked]
maria_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in maria_blocked]
william_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in william_blocked]

# Combine all constraints
constraints = billy_constraints + maria_constraints + william_constraints

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