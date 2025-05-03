from z3 import *

# Define the blocked intervals for each person in minutes
billy_blocked = [
    (600, 630),   # 10:00-10:30
    (690, 720),   # 11:30-12:00
    (840, 870),   # 14:00-14:30
    (990, 1020)   # 16:30-17:00
]

patricia_blocked = [
    (540, 750),   # 9:00-12:30
    (810, 840),   # 13:30-14:00
    (870, 960),   # 14:30-16:00
    (990, 1020)   # 16:30-17:00
]

# Considering Billy's preference to avoid meetings after 15:30 (930 minutes),
# the latest possible start time is 15:00 (900 minutes)
# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
billy_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in billy_blocked]
patricia_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in patricia_blocked]

# Combine all constraints
constraints = billy_constraints + patricia_constraints

# Add the constraints for the valid time range, considering Billy's preference
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