from z3 import *

# Define the blocked intervals for each person in minutes
brandon_blocked = [
    (690, 720),   # 11:30-12:00
    (750, 810),   # 12:30-13:30
    (840, 870)    # 14:00-14:30
]

donna_blocked = [
    (600, 630),   # 10:00-10:30
    (720, 750)    # 12:00-12:30
]

jack_blocked = [
    (570, 600),   # 9:30-10:00
    (630, 660),   # 10:30-11:00
    (690, 750),   # 11:30-12:30
    (780, 870),   # 13:00-14:30
    (930, 1020)   # 15:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
brandon_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in brandon_blocked]
donna_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in donna_blocked]
jack_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in jack_blocked]

# Combine all constraints
constraints = brandon_constraints + donna_constraints + jack_constraints

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