from z3 import *

# Define the blocked intervals for each person in minutes
richard_blocked = [
    (810, 840),   # 13:30-14:00
    (900, 930)    # 15:00-15:30
]

martha_blocked = [
    (540, 570),   # 9:00-9:30
    (780, 810)    # 13:00-13:30
]

kimberly_blocked = [
    (540, 660),   # 9:00-11:00
    (690, 720),   # 11:30-12:00
    (750, 780),   # 12:30-13:00
    (840, 960)    # 14:00-16:00
]

# Create the variable for the start time, considering Martha's preference
t = Int('t')

# Create constraints for each person's blocked times
richard_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in richard_blocked]
martha_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in martha_blocked]
kimberly_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in kimberly_blocked]

# Combine all constraints
constraints = richard_constraints + martha_constraints + kimberly_constraints

# Add the constraints for the valid time range, considering Martha's preference
constraints.append(840 <= t)  # Earliest start time is 14:00 (840 minutes)
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