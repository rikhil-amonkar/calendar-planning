from z3 import *

# Define the blocked intervals for each person in minutes
kathryn_blocked = [
    (540, 570),   # 9:00-9:30
    (630, 660),   # 10:30-11:00
    (690, 720),   # 11:30-12:00
    (810, 870),   # 13:30-14:30
    (990, 1020)   # 16:30-17:00
]

charlotte_blocked = [
    (720, 750),   # 12:00-12:30
    (960, 990)    # 16:00-16:30
]
# Charlotte's preference: no meetings after 13:30 (810 minutes), so meeting must end by 13:30
# Thus, latest start time is 13:00 (780 minutes)

lauren_blocked = [
    (540, 600),   # 9:00-10:00
    (720, 750),   # 12:00-12:30
    (810, 870),   # 13:30-14:30
    (900, 960),   # 15:00-16:00
    (990, 1020)   # 16:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
kathryn_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in kathryn_blocked]
charlotte_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in charlotte_blocked]
lauren_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in lauren_blocked]

# Combine all constraints
constraints = kathryn_constraints + charlotte_constraints + lauren_constraints

# Add the constraints for the valid time range, considering Charlotte's preference
constraints.append(540 <= t)
constraints.append(t <= 780)

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