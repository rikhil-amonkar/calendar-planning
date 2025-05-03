from z3 import *

# Define the blocked intervals for each person in minutes
arthur_blocked = [
    (540, 570),   # 9:00-9:30
    (630, 720),   # 10:30-12:00
    (960, 1020)   # 16:00-17:00
]

michael_blocked = [
    (780, 810),   # 13:00-13:30
    (840, 870)    # 14:00-14:30
]

samantha_blocked = [
    (630, 660),   # 10:30-11:00
    (720, 900),   # 12:00-15:00
    (930, 1020)   # 15:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
arthur_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in arthur_blocked]
michael_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in michael_blocked]
samantha_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in samantha_blocked]

# Combine all constraints
constraints = arthur_constraints + michael_constraints + samantha_constraints

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