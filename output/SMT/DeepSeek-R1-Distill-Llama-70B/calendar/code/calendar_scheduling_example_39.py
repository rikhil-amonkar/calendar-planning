from z3 import *

# Define the blocked intervals for each person in minutes
victoria_blocked = [
    (810, 840),   # 13:30-14:00
    (870, 930),   # 14:30-15:30
    (990, 1020)   # 16:30-17:00
]

nancy_blocked = [
    (540, 840),   # 9:00-14:00
    (870, 930)    # 14:30-15:30
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
victoria_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in victoria_blocked]
nancy_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in nancy_blocked]

# Combine all constraints
constraints = victoria_constraints + nancy_constraints

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