from z3 import *

# Define the blocked intervals for each person in minutes
diane_blocked = [
    (540, 570),   # 9:00-9:30
    (720, 750),   # 12:00-12:30
    (870, 930)    # 14:30-15:30
]

kelly_blocked = [
    (570, 600),   # 9:30-10:00
    (630, 660)    # 10:30-11:00
]

deborah_blocked = [
    (540, 570),   # 9:00-9:30
    (600, 840),   # 10:00-14:00
    (870, 1020)   # 14:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
diane_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in diane_blocked]
kelly_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in kelly_blocked]
deborah_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in deborah_blocked]

# Combine all constraints
constraints = diane_constraints + kelly_constraints + deborah_constraints

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