from z3 import *

# Define the blocked intervals for each person in minutes
gregory_blocked = [
    (660, 690),   # 11:00-11:30
    (720, 750),   # 12:00-12:30
    (930, 990)    # 15:30-16:30
]

carol_blocked = [
    (540, 630),   # 9:00-10:30
    (660, 960),   # 11:00-16:00
    (990, 1020)   # 16:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
gregory_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in gregory_blocked]
carol_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in carol_blocked]

# Combine all constraints
constraints = gregory_constraints + carol_constraints

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