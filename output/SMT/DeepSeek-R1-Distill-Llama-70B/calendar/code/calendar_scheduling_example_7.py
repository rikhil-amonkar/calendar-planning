from z3 import *

# Define the blocked intervals for each person in minutes
heather_blocked = [
    (540, 570),   # 9:00-9:30
    (630, 660),   # 10:30-11:00
    (780, 840),   # 13:00-14:00
    (870, 900),   # 14:30-15:00
    (960, 990)    # 16:00-16:30
]

nicholas_blocked = []  # Nicholas has no meetings

zachary_blocked = [
    (540, 630),   # 9:00-10:30
    (660, 720),   # 11:00-12:00
    (750, 780),   # 12:30-13:00
    (810, 990)    # 13:30-16:30
]

# Considering Zachary's preference to not meet after 14:00 (840 minutes),
# the latest possible start time is 13:30 (810 minutes)
# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
heather_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in heather_blocked]
zachary_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in zachary_blocked]

# Combine all constraints
constraints = heather_constraints + zachary_constraints

# Add the constraints for the valid time range, considering Zachary's preference
constraints.append(540 <= t)
constraints.append(t <= 810)

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