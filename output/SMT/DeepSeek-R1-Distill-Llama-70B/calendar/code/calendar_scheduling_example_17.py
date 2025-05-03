from z3 import *

# Define the blocked intervals for each person in minutes
margaret_blocked = [
    (540, 600),   # 9:00-10:00
    (630, 660),   # 10:30-11:00
    (690, 720),   # 11:30-12:00
    (780, 810),   # 13:00-13:30
    (900, 930)    # 15:00-15:30
]

donna_blocked = [
    (870, 900),   # 14:30-15:00
    (960, 990)    # 16:00-16:30
]

helen_blocked = [
    (540, 570),   # 9:00-9:30
    (600, 690),   # 10:00-11:30
    (780, 840),   # 13:00-14:00
    (870, 900),   # 14:30-15:00
    (930, 1020)   # 15:30-17:00
]

# Considering Helen's preference to not meet after 13:30 (810 minutes),
# the latest possible start time is 13:00 (780 minutes)
# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
margaret_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in margaret_blocked]
donna_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in donna_blocked]
helen_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in helen_blocked]

# Combine all constraints
constraints = margaret_constraints + donna_constraints + helen_constraints

# Add the constraints for the valid time range, considering Helen's preference
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