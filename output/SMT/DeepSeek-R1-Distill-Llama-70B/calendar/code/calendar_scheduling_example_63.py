from z3 import *

# Blocked intervals in minutes
judith_blocked = [
    (600, 630),  # 10:00 AM - 10:30 AM
    (660, 720),  # 11:00 AM - 12:00 PM
    (750, 780)   # 12:30 PM - 1:00 PM
]

roger_blocked = [
    (540, 570),  # 9:00 AM - 9:30 AM
    (630, 660),  # 10:30 AM - 11:00 AM
    (720, 750),  # 12:00 PM - 12:30 PM
    (780, 810),  # 1:00 PM - 1:30 PM
    (840, 960)   # 2:00 PM - 4:00 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Judith's constraints
for s, e in judith_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Roger's constraints
for s, e in roger_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Add constraints for valid time range
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 960)  # 4:00 PM

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