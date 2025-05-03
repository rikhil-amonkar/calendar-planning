from z3 import *

# Define the blocked intervals for each person in minutes
diana_blocked = [
    (690, 720),   # 11:30-12:00
    (780, 810)    # 13:00-13:30
]

ethan_blocked = []  # Ethan has no meetings

janet_blocked = [
    (540, 600),   # 9:00-10:00
    (750, 780),   # 12:30-13:00
    (840, 900),   # 14:00-15:00
    (930, 1020)   # 15:30-17:00
]

# Considering Janet's preference to not meet after 12:00 (720 minutes),
# the latest possible start time is 11:30 (690 minutes)
# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
diana_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in diana_blocked]
janet_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in janet_blocked]

# Combine all constraints
constraints = diana_constraints + janet_constraints

# Add the constraints for the valid time range, considering Janet's preference
constraints.append(540 <= t)
constraints.append(t <= 690)

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