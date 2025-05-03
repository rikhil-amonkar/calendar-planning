from z3 import *

# Blocked intervals in minutes
john_blocked = [
    (750, 780),  # 12:30 PM - 1:00 PM
    (930, 960)   # 3:30 PM - 4:00 PM
]

andrea_blocked = [
    (540, 570),  # 9:00 AM - 9:30 AM
    (660, 750),  # 11:00 AM - 12:30 PM
    (900, 930),  # 3:00 PM - 3:30 PM
    (960, 990)   # 4:00 PM - 4:30 PM
]

lisa_blocked = [
    (540, 600),  # 9:00 AM - 10:00 AM
    (630, 660),  # 10:30 AM - 11:00 AM
    (720, 750),  # 12:00 PM - 12:30 PM
    (780, 900),  # 2:00 PM - 3:30 PM
    (960, 990)   # 4:00 PM - 4:30 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# John's constraints
for s, e in john_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Andrea's constraints
for s, e in andrea_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Lisa's constraints
for s, e in lisa_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Additional constraints based on preferences and valid time range
constraints.append(540 <= t)  # Start time >= 9:00 AM
constraints.append(t <= 960)  # Start time <= 4:00 PM

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