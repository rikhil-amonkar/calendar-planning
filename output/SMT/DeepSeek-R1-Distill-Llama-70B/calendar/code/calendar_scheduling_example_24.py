from z3 import *

# Define the blocked intervals for Brenda in minutes
brenda_blocked = [
    (570, 600),   # 9:30-10:00
    (690, 750),   # 11:30-12:30
    (840, 990)    # 14:00-16:30
]

# Considering Benjamin's preference to not meet after 9:30 (570 minutes),
# the latest possible start time is 9:30 (570 minutes)
# Create the variable for the start time
t = Int('t')

# Create constraints for Brenda's blocked times
brenda_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in brenda_blocked]

# Combine all constraints
constraints = brenda_constraints

# Add the constraints for the valid time range, considering Benjamin's preference
constraints.append(540 <= t)  # Earliest start time is 9:00 (540 minutes)
constraints.append(t <= 570)  # Latest start time is 9:30 (570 minutes)

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