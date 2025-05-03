from z3 import *

# Define the blocked intervals for each person in minutes
gerald_blocked = [
    (540, 570),   # 9:00-9:30
    (780, 840),   # 13:00-14:00
    (900, 930),   # 15:00-15:30
    (960, 1020)   # 16:00-17:00
]

roy_blocked = []  # Roy has no meetings

barbara_blocked = [
    (570, 600),   # 9:30-10:00
    (690, 840),   # 11:30-14:00
    (870, 900),   # 14:30-15:00
    (930, 1020)   # 15:30-17:00
]

# Considering Gerald's preference to avoid meetings before 13:00 (780 minutes),
# the earliest possible start time is 13:00 (780 minutes)
# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
gerald_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in gerald_blocked]
barbara_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in barbara_blocked]

# Combine all constraints
constraints = gerald_constraints + barbara_constraints

# Add the constraints for the valid time range, considering Gerald's preference
constraints.append(780 <= t)
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