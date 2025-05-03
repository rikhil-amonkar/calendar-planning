from z3 import *

# Define the blocked intervals for each person in minutes
emily_blocked = [
    (600, 630),   # 10:00-10:30
    (690, 750),   # 11:30-12:30
    (840, 900),   # 14:00-15:00
    (960, 990)    # 16:00-16:30
]

melissa_blocked = [
    (570, 600),   # 9:30-10:00
    (870, 900)    # 14:30-15:00
]

frank_blocked = [
    (600, 630),   # 10:00-10:30
    (660, 690),   # 11:00-11:30
    (750, 780),   # 12:30-13:00
    (810, 870),   # 13:30-14:30
    (900, 960),   # 15:00-16:00
    (990, 1020)   # 16:30-17:00
]

# Create the variable for the start time, considering Frank's preference
t = Int('t')

# Create constraints for each person's blocked times
emily_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in emily_blocked]
melissa_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in melissa_blocked]
frank_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in frank_blocked]

# Combine all constraints
constraints = emily_constraints + melissa_constraints + frank_constraints

# Add the constraints for the valid time range, considering Frank's preference
constraints.append(540 <= t)  # Earliest start time is 9:00 (540 minutes)
constraints.append(t <= 570)  # Latest start time is 9:30 (570 minutes)

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