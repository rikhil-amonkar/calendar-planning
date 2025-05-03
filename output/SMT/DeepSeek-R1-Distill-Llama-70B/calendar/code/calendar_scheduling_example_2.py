from z3 import *

# Define the blocked intervals for each person in minutes
roy_blocked = [
    (540, 570),   # 9:00-9:30
    (600, 630),   # 10:00-10:30
    (660, 690),   # 11:00-11:30
    (750, 780)    # 12:30-13:00
]

kathryn_blocked = [
    (570, 600),   # 9:30-10:00
    (990, 1020)   # 16:30-17:00
]

amy_blocked = [
    (540, 870),   # 9:00-14:30
    (900, 960),   # 15:00-16:00
    (990, 1020)   # 16:30-17:00
]

# Considering Amy's preference to not meet after 15:30 (930 minutes),
# the latest possible start time is 15:00 (900 minutes)
# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
roy_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in roy_blocked]
kathryn_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in kathryn_blocked]
amy_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in amy_blocked]

# Combine all constraints
constraints = roy_constraints + kathryn_constraints + amy_constraints

# Add the constraints for the valid time range, considering Amy's preference
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