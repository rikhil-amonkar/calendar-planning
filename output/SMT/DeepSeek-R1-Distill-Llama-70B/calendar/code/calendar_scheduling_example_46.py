from z3 import *

# Define the blocked intervals for each person in minutes
arthur_blocked = [
    (570, 600),   # 9:30-10:00
    (840, 870)    # 14:00-14:30
]

theresa_blocked = [
    (540, 570),   # 9:00-9:30
    (720, 780),   # 12:00-13:00
    (900, 990)    # 15:00-16:30
]

carl_blocked = [
    (540, 690),   # 9:00-11:30
    (720, 840),   # 12:00-14:00
    (870, 1020)   # 14:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
arthur_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in arthur_blocked]
theresa_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in theresa_blocked]
carl_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in carl_blocked]

# Combine all constraints
constraints = arthur_constraints + theresa_constraints + carl_constraints

# Add the constraints for the valid time range
constraints.append(540 <= t)  # 9:00
constraints.append(t <= 990)  # 16:30

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