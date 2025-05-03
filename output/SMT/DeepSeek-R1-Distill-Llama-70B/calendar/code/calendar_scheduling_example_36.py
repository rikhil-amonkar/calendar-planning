from z3 import *

# Define the blocked intervals for each person in minutes
ryan_blocked = [
    (540, 570),   # 9:00-9:30
    (750, 780)    # 12:30-13:00
]

denise_blocked = [
    (570, 630),   # 9:30-10:30
    (720, 780),   # 12:00-13:00
    (870, 990)    # 14:30-16:30
]

# Create the variable for the start time, considering Denise's preference
t = Int('t')

# Create constraints for each person's blocked times
ryan_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in ryan_blocked]
denise_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in denise_blocked]

# Combine all constraints
constraints = ryan_constraints + denise_constraints

# Add the constraints for the valid time range, considering Denise's preference
constraints.append(540 <= t)  # Earliest start time is 9:00 (540 minutes)
constraints.append(t <= 750)  # Latest start time is 12:30 (750 minutes)

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