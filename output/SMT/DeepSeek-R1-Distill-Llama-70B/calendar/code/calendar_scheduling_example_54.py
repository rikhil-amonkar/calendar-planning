from z3 import *

# Define the blocked intervals for each person in minutes
isabella_blocked = [
    (660, 690),   # 11:00-11:30
    (930, 960)    # 15:30-16:00
]

tyler_blocked = [
    (540, 600)    # 9:00-10:00
]

jordan_blocked = [
    (540, 600),   # 9:00-10:00
    (630, 660),   # 10:30-11:00
    (750, 810),   # 12:30-13:30
    (840, 870),   # 14:00-14:30
    (900, 960)    # 15:00-16:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
isabella_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in isabella_blocked]
tyler_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in tyler_blocked]
jordan_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in jordan_blocked]

# Combine all constraints
constraints = isabella_constraints + tyler_constraints + jordan_constraints

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