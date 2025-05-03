from z3 import *

# Define the blocked intervals for each person in minutes
alice_blocked = [
    (570, 600),   # 9:30-10:00
    (750, 780),   # 12:30-13:00
    (870, 900),   # 14:30-15:00
    (990, 1020)   # 16:30-17:00
]

arthur_blocked = [
    (540, 570),   # 9:00-9:30
    (600, 660),   # 10:00-11:00
    (690, 720),   # 11:30-12:00
    (780, 840),   # 13:00-14:00
    (900, 930),   # 15:00-15:30
    (990, 1020)   # 16:30-17:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
alice_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in alice_blocked]
arthur_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in arthur_blocked]

# Combine all constraints
constraints = alice_constraints + arthur_constraints

# Add the constraints for the valid time range
constraints.append(540 <= t)
constraints.append(t <= 900)

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