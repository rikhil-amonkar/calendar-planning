from z3 import *

# Define the blocked intervals for each person in minutes
jesse_blocked = [
    (600, 630),   # 10:00-10:30
    (930, 960)    # 15:30-16:00
]

megan_blocked = [
    (630, 660),   # 10:30-11:00
    (690, 750),   # 11:30-12:30
    (810, 870),   # 13:30-14:30
    (900, 990)    # 15:00-16:30
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
jesse_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in jesse_blocked]
megan_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in megan_blocked]

# Combine all constraints
constraints = jesse_constraints + megan_constraints

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