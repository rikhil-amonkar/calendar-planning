from z3 import *

# Define the blocked intervals for each person in minutes
anthony_blocked = [
    (570, 600),   # 9:30-10:00
    (720, 780),   # 12:00-13:00
    (960, 990)    # 16:00-16:30
]

pamela_blocked = [
    (570, 600),   # 9:30-10:00
    (990, 1020)   # 16:30-17:00
]

zachary_blocked = [
    (540, 690),   # 9:00-11:30
    (720, 750),   # 12:00-12:30
    (780, 810),   # 13:00-13:30
    (870, 900),   # 14:30-15:00
    (960, 1020)   # 16:00-17:00
]

# Create the variable for the start time, considering Pamela's preference
t = Int('t')

# Create constraints for each person's blocked times
anthony_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in anthony_blocked]
pamela_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in pamela_blocked]
zachary_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in zachary_blocked]

# Combine all constraints
constraints = anthony_constraints + pamela_constraints + zachary_constraints

# Add the constraints for the valid time range, considering Pamela's preference
constraints.append(540 <= t)  # Earliest start time is 9:00 (540 minutes)
constraints.append(t <= 870)  # Latest start time is 14:30 (870 minutes)

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