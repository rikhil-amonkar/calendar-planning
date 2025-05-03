from z3 import *

# Define the blocked intervals for each person in minutes
zachary_blocked = [
    (600, 630),   # 10:00-10:30
    (900, 930)    # 15:00-15:30
]

teresa_blocked = [
    (540, 630),   # 9:00-10:30
    (660, 750),   # 11:00-12:30
    (780, 840),   # 13:00-14:00
    (870, 990)    # 14:30-16:30
]

# Create the variable for the start time, considering Bradley's preference
t = Int('t')

# Create constraints for each person's blocked times
zachary_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in zachary_blocked]
teresa_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in teresa_blocked]

# Combine all constraints
constraints = zachary_constraints + teresa_constraints

# Add the constraints for the valid time range, considering Bradley's preference
constraints.append(870 <= t)  # Earliest start time is 14:30 (870 minutes)
constraints.append(t <= 990)  # Latest start time is 16:30 (990 minutes)

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