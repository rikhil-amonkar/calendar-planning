from z3 import *

# Define the blocked intervals for each person in minutes
keith_blocked = [
    (840, 870),   # 14:00-14:30
    (960, 990)    # 16:00-16:30
]

cynthia_blocked = [
    (540, 630),   # 9:00-10:30
    (690, 1020)   # 11:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
keith_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in keith_blocked]
cynthia_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in cynthia_blocked]

# Combine all constraints
constraints = keith_constraints + cynthia_constraints

# Add the constraints for the valid time range
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 900)  # 3:00 PM

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