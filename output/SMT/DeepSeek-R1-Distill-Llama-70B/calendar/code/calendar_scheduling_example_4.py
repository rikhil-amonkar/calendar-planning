from z3 import *

# Define the blocked intervals for each person in minutes
donna_blocked = [
    (840, 870),   # 14:00-14:30
    (930, 960)    # 15:30-16:00
]

john_blocked = [
    (660, 690),   # 11:00-11:30
    (990, 1020)   # 16:30-17:00
]

billy_blocked = [
    (540, 600),   # 9:00-10:00
    (630, 840),   # 10:30-14:00
    (870, 1020)   # 14:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
donna_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in donna_blocked]
john_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in john_blocked]
billy_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in billy_blocked]

# Combine all constraints
constraints = donna_constraints + john_constraints + billy_constraints

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