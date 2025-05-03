from z3 import *

# Define the blocked intervals for each person in minutes
richard_blocked = [
    (600, 630),   # 10:00-10:30
    (660, 720),   # 11:00-12:00
    (780, 840),   # 13:00-14:00
    (960, 990)    # 16:00-16:30
]

noah_blocked = [
    (600, 630),   # 10:00-10:30
    (690, 780),   # 11:30-13:00
    (810, 840),   # 13:30-14:00
    (870, 1020)   # 14:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
richard_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in richard_blocked]
noah_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in noah_blocked]

# Combine all constraints
constraints = richard_constraints + noah_constraints

# Add the constraints for the valid time range
constraints.append(540 <= t)  # 9:00
constraints.append(t <= 960)  # 16:00

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