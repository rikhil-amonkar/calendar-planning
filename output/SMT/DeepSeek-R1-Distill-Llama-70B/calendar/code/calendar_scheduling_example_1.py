from z3 import *

# Define the blocked intervals for each person in minutes
raymond_blocked = [
    (540, 570),   # 9:00-9:30
    (690, 720),   # 11:30-12:00
    (780, 810),   # 13:00-13:30
    (900, 930)    # 15:00-15:30
]

billy_blocked = [
    (600, 630),   # 10:00-10:30
    (720, 780),   # 12:00-13:00
    (990, 1020)   # 16:30-17:00
]
# Additionally, Billy prefers no meetings after 15:00, so meeting must end by 15:00 (900 minutes)
# Thus, latest start time is 14:30 (870 minutes)

donald_blocked = [
    (540, 570),   # 9:00-9:30
    (600, 660),   # 10:00-11:00
    (720, 780),   # 12:00-13:00
    (840, 870),   # 14:00-14:30
    (960, 1020)   # 16:00-17:00
]

# Create the variable for the start time, constrained to 9:00-14:30 (540 to 870 minutes)
t = Int('t')

# Create constraints for each person's blocked times
raymond_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in raymond_blocked]
billy_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in billy_blocked]
donald_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in donald_blocked]

# Combine all constraints
constraints = raymond_constraints + billy_constraints + donald_constraints

# Add the constraints for the valid time range, considering Billy's preference
constraints.append(540 <= t)
constraints.append(t <= 870)

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