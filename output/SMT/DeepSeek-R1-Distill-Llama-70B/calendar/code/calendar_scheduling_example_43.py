from z3 import *

# Define the blocked intervals for each person in minutes
albert_blocked = [
    (570, 630),   # 9:30-10:30
    (720, 750),   # 12:00-12:30
    (840, 870),   # 14:00-14:30
    (900, 930),   # 15:00-15:30
    (990, 1020)   # 16:30-17:00
]

gregory_blocked = [
    (660, 690),   # 11:00-11:30
    (750, 780),   # 12:30-13:00
    (810, 840),   # 13:30-14:00
    (930, 960)    # 15:30-16:00
]

benjamin_blocked = [
    (570, 600),   # 9:30-10:00
    (630, 660),   # 10:30-11:00
    (690, 810),   # 11:30-13:30
    (840, 900),   # 14:00-15:00
    (930, 960),   # 15:30-16:00
    (990, 1020)   # 16:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
albert_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in albert_blocked]
gregory_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in gregory_blocked]
benjamin_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in benjamin_blocked]

# Combine all constraints
constraints = albert_constraints + gregory_constraints + benjamin_constraints

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