from z3 import *

# Define the blocked intervals for Samuel in minutes
samuel_blocked = [
    (540, 630),   # 9:00-10:30
    (690, 720),   # 11:30-12:00
    (780, 810),   # 13:00-13:30
    (840, 960),   # 14:00-16:00
    (990, 1020)   # 16:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for Samuel's blocked times
samuel_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in samuel_blocked]

# Combine all constraints
constraints = samuel_constraints

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