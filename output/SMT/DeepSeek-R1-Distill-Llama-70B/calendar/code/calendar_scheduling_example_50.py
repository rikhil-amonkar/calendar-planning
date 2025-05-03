from z3 import *

# Define the blocked intervals for Emma in minutes
emma_blocked = [
    (540, 630),   # 9:00-10:30
    (660, 720),   # 11:00-12:00
    (750, 810),   # 12:30-13:30
    (870, 930),   # 14:30-15:30
    (960, 990)    # 16:00-16:30
]

# Create the variable for the start time
t = Int('t')

# Create constraints for Emma's blocked times
emma_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in emma_blocked]

# Combine all constraints
constraints = emma_constraints

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