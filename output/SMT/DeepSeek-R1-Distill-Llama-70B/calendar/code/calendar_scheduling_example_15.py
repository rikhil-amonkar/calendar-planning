from z3 import *

# Define the blocked intervals for each person in minutes
joyce_blocked = [
    (660, 690),   # 11:00-11:30
    (810, 840),   # 13:30-14:00
    (870, 990)    # 14:30-16:30
]

christine_blocked = []  # Christine has no meetings but cannot meet before 12:00
# Implicit constraint: t >= 720 (12:00)

alexander_blocked = [
    (540, 660),   # 9:00-11:00
    (720, 750),   # 12:00-12:30
    (810, 900),   # 13:30-15:00
    (930, 960),   # 15:30-16:00
    (990, 1020)   # 16:30-17:00
]

# Create the variable for the start time, considering Christine's preference
t = Int('t')

# Create constraints for each person's blocked times
joyce_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in joyce_blocked]
alexander_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in alexander_blocked]

# Combine all constraints
constraints = joyce_constraints + alexander_constraints

# Add the constraints for the valid time range, considering Christine's preference
constraints.append(720 <= t)  # Earliest start time is 12:00 (720 minutes)
constraints.append(t <= 990)  # Latest start time is 16:30 (990 minutes)

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