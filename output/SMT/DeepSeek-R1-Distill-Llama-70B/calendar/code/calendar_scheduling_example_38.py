from z3 import *

# Define the blocked intervals for each person in minutes
catherine_blocked = [
    (630, 660),   # 10:30-11:00
    (750, 810),   # 12:30-13:30
    (870, 900)    # 14:30-15:00
]

michael_blocked = [
    (570, 630),   # 9:30-10:30
    (720, 780),   # 12:00-13:00
    (810, 840),   # 13:30-14:00
    (900, 930)    # 15:00-15:30
]

alexander_blocked = [
    (540, 570),   # 9:00-9:30
    (600, 630),   # 10:00-10:30
    (660, 720),   # 11:00-12:00
    (780, 810),   # 13:00-13:30
    (840, 960),   # 14:00-16:00
    (990, 1020)   # 16:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
catherine_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in catherine_blocked]
michael_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in michael_blocked]
alexander_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in alexander_blocked]

# Combine all constraints
constraints = catherine_constraints + michael_constraints + alexander_constraints

# Add the constraints for the valid time range
constraints.append(540 <= t)
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