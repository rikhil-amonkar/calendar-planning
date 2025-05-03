from z3 import *

# Define the blocked intervals for each person in minutes
brittany_blocked = [
    (780, 810),   # 13:00-13:30
    (960, 990)    # 16:00-16:30
]

doris_blocked = [
    (540, 660),   # 9:00-11:00
    (690, 870),   # 11:30-14:30
    (900, 1020)   # 15:00-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
brittany_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in brittany_blocked]
doris_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in doris_blocked]

# Combine all constraints
constraints = brittany_constraints + doris_constraints

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