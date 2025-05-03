from z3 import *

# Blocked intervals in minutes
michael_blocked = [
    (600, 630),  # 10:00 AM - 10:30 AM
    (690, 720),  # 11:30 AM - 12:00 PM
    (810, 840),  # 1:30 PM - 2:00 PM
    (930, 960)   # 3:30 PM - 4:00 PM
]

lauren_blocked = [
    (540, 630),  # 9:00 AM - 10:30 AM
    (870, 1020)  # 2:30 PM - 5:00 PM
]

t = Int('t')

# Create constraints for Michael's blocked times
michael_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in michael_blocked]

# Create constraints for Lauren's blocked times
lauren_constraints = [Or(t + 30 <= s, t >= e) for (s, e) in lauren_blocked]

# Combine all constraints
constraints = michael_constraints + lauren_constraints

# Add constraints for valid time range
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 990)  # 4:30 PM

# Create solver and solve
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    start_time = model[t].as_long()
    hours = start_time // 60
    minutes = start_time % 60
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No solution found")