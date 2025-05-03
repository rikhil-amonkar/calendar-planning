from z3 import *

# Define the blocked intervals for each person in minutes
adam_blocked = [
    (600, 630),   # 10:00-10:30
    (750, 780),   # 12:30-13:00
    (810, 870)    # 13:30-14:30
]

jerry_blocked = [
    (540, 570),   # 9:00-9:30
    (720, 750),   # 12:00-12:30
    (900, 960)    # 15:00-16:00
]

matthew_blocked = [
    (570, 660),   # 9:30-11:00
    (690, 750),   # 11:30-12:30
    (780, 840),   # 13:00-14:00
    (870, 1020)   # 14:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
adam_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in adam_blocked]
jerry_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in jerry_blocked]
matthew_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in matthew_blocked]

# Combine all constraints
constraints = adam_constraints + jerry_constraints + matthew_constraints

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