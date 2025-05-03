from z3 import *

# Define the blocked intervals for each person in minutes
julie_blocked = [
    (540, 570),   # 9:00-9:30
    (660, 690),   # 11:00-11:30
    (720, 750),   # 12:00-12:30
    (810, 840),   # 13:30-14:00
    (960, 1020)   # 16:00-17:00
]

sean_blocked = [
    (540, 570),   # 9:00-9:30
    (780, 810),   # 13:00-13:30
    (900, 930),   # 15:00-15:30
    (960, 990)    # 16:00-16:30
]

lori_blocked = [
    (600, 630),   # 10:00-10:30
    (660, 780),   # 11:00-13:00
    (930, 1020)   # 15:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
julie_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in julie_blocked]
sean_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in sean_blocked]
lori_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in lori_blocked]

# Combine all constraints
constraints = julie_constraints + sean_constraints + lori_constraints

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