from z3 import *

# Define the blocked intervals for each person in minutes
eric_blocked = [
    (540, 570),   # 9:00-9:30
    (630, 690),   # 10:30-11:30
    (900, 930)    # 15:00-15:30
]

roger_blocked = [
    (570, 630),   # 9:30-10:30
    (660, 720),   # 11:00-12:00
    (750, 780),   # 12:30-13:00
    (870, 900),   # 14:30-15:00
    (930, 990)    # 15:30-16:30
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
eric_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in eric_blocked]
roger_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in roger_blocked]

# Combine all constraints
constraints = eric_constraints + roger_constraints

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