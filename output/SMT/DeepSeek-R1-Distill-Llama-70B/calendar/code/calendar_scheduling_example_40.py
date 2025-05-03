from z3 import *

# Define the blocked intervals for each person in minutes
jacob_blocked = [
    (600, 660),   # 10:00-11:00
    (690, 720),   # 11:30-12:00
    (960, 990)    # 16:00-16:30
]

gabriel_blocked = [
    (570, 690),   # 9:30-11:30
    (780, 810),   # 13:00-13:30
    (900, 930)    # 15:00-15:30
]

matthew_blocked = [
    (540, 570),   # 9:00-9:30
    (630, 660),   # 10:30-11:00
    (690, 720),   # 11:30-12:00
    (750, 840),   # 12:30-14:00
    (930, 990)    # 15:30-16:30
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
jacob_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in jacob_blocked]
gabriel_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in gabriel_blocked]
matthew_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in matthew_blocked]

# Combine all constraints
constraints = jacob_constraints + gabriel_constraints + matthew_constraints

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