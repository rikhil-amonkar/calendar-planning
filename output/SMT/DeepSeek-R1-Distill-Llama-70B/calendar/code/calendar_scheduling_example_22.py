from z3 import *

# Define the blocked intervals for each person in minutes
theresa_blocked = [
    (540, 570),   # 9:00-9:30
    (750, 810),   # 12:30-13:30
    (840, 900),   # 14:00-15:00
    (990, 1020)   # 16:30-17:00
]

charles_blocked = [
    (600, 630),   # 10:00-10:30
    (690, 750),   # 11:30-12:30
    (840, 930)    # 14:00-15:30
]

betty_blocked = [
    (540, 630),   # 9:00-10:30
    (720, 750),   # 12:00-12:30
    (780, 840),   # 13:00-14:00
    (900, 960)    # 15:00-16:00
]

# Create the variable for the start time
t = Int('t')

# Create constraints for each person's blocked times
theresa_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in theresa_blocked]
charles_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in charles_blocked]
betty_constraints = [Or(t + 60 <= s, t >= e) for (s, e) in betty_blocked]

# Combine all constraints
constraints = theresa_constraints + charles_constraints + betty_constraints

# Add the constraints for the valid time range
constraints.append(540 <= t)
constraints.append(t <= 960)

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