from z3 import *

# Define the blocked intervals for each person in minutes
thomas_blocked = []  # Thomas is available all day

dylan_blocked = [
    (630, 660),   # 10:30-11:00
    (810, 840)    # 13:30-14:00
]

jerry_blocked = [
    (540, 660),   # 9:00-11:00
    (690, 870),   # 11:30-14:30
    (960, 1020)   # 16:00-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
dylan_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in dylan_blocked]
jerry_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in jerry_blocked]

# Combine all constraints
constraints = dylan_constraints + jerry_constraints

# Add the constraints for the valid time range
constraints.append(540 <= t)
constraints.append(t <= 960)

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