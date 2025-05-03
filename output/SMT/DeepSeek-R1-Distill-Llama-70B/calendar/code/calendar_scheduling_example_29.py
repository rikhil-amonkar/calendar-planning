from z3 import *

# Define the blocked intervals for each person in minutes
madison_blocked = [
    (570, 600),   # 9:30-10:00
    (690, 720)    # 11:30-12:00
]

diana_blocked = [
    (660, 690),   # 11:00-11:30
    (780, 810)    # 13:00-13:30
]

shirley_blocked = [
    (540, 720),   # 9:00-12:00
    (810, 900),   # 13:30-15:00
    (930, 1020)   # 15:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
madison_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in madison_blocked]
diana_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in diana_blocked]
shirley_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in shirley_blocked]

# Combine all constraints
constraints = madison_constraints + diana_constraints + shirley_constraints

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