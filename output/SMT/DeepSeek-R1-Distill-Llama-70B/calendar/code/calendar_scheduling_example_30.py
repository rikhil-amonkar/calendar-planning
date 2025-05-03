from z3 import *

# Define the blocked intervals for each person in minutes
jeffrey_blocked = [
    (570, 600),   # 9:30-10:00
    (630, 660)    # 10:30-11:00
]

virginia_blocked = [
    (540, 570),   # 9:00-9:30
    (600, 630),   # 10:00-10:30
    (870, 900),   # 14:30-15:00
    (960, 990)    # 16:00-16:30
]

melissa_blocked = [
    (540, 690),   # 9:00-11:30
    (720, 750),   # 12:00-12:30
    (780, 900),   # 13:00-15:00
    (960, 1020)   # 16:00-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
jeffrey_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in jeffrey_blocked]
virginia_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in virginia_blocked]
melissa_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in melissa_blocked]

# Combine all constraints
constraints = jeffrey_constraints + virginia_constraints + melissa_constraints

# Add the constraints for the valid time range, considering Melissa's preference
constraints.append(540 <= t)  # Earliest start time is 9:00 (540 minutes)
constraints.append(t <= 810)  # Latest start time is 13:30 (810 minutes)

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