from z3 import *

# Define the blocked intervals for each person in minutes
ralph_blocked = [
    (810, 840),   # 13:30-14:00
    (870, 900)    # 14:30-15:00
]

peter_blocked = [
    (540, 570),   # 9:00-9:30
    (660, 780),   # 11:00-13:00
    (960, 990)    # 16:00-16:30
]

daniel_blocked = [
    (540, 600),   # 9:00-10:00
    (630, 930),   # 10:30-15:30
    (960, 1020)   # 16:00-17:00
]

# Considering Daniel's preference to not meet after 13:30 (810 minutes),
# the latest possible start time is 13:00 (780 minutes)
# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
ralph_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in ralph_blocked]
peter_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in peter_blocked]
daniel_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in daniel_blocked]

# Combine all constraints
constraints = ralph_constraints + peter_constraints + daniel_constraints

# Add the constraints for the valid time range, considering Daniel's preference
constraints.append(540 <= t)
constraints.append(t <= 780)

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