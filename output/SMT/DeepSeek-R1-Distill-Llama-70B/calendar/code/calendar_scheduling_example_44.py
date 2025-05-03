from z3 import *

# Define the blocked intervals for each person in minutes
ronald_blocked = [
    (690, 720),   # 11:30-12:00
    (840, 870),   # 14:00-14:30
    (960, 1020)   # 16:00-17:00
]

amanda_blocked = [
    (570, 720),   # 9:30-12:00
    (750, 780),   # 12:30-13:00
    (810, 840),   # 13:30-14:00
    (930, 1020)   # 15:30-17:00
]

# Create the variable for the start time, considering Isabella's preference
t = Int('t')

# Create constraints for each person's blocked times
ronald_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in ronald_blocked]
amanda_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in amanda_blocked]

# Combine all constraints
constraints = ronald_constraints + amanda_constraints

# Add the constraints for the valid time range, considering Isabella's preference
constraints.append(540 <= t)  # Earliest start time is 9:00 (540 minutes)
constraints.append(t <= 780)  # Latest start time is 13:00 (780 minutes)

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