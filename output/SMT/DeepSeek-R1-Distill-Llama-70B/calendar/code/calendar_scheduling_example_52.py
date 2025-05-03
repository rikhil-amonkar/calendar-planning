from z3 import *

# Define the blocked intervals for each person in minutes
grace_blocked = [
    (540, 570),   # 9:00-9:30
    (600, 660),   # 10:00-11:00
    (960, 990)    # 16:00-16:30
]

randy_blocked = [
    (750, 780),   # 12:30-13:00
    (960, 990)    # 16:00-16:30
]

susan_blocked = [
    (540, 870),   # 9:00-14:30
    (930, 960)    # 15:30-16:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
grace_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in grace_blocked]
randy_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in randy_blocked]
susan_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in susan_blocked]

# Combine all constraints
constraints = grace_constraints + randy_constraints + susan_constraints

# Add the constraints for the valid time range
constraints.append(540 <= t)
constraints.append(t <= 900)

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