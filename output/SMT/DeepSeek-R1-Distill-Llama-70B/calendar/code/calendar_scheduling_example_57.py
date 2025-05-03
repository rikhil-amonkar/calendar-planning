from z3 import *

# Blocked intervals in minutes
virginia_blocked = [
    (600, 720)  # 10:00 AM - 12:00 PM
]

charles_blocked = [
    (720, 750),  # 12:00 PM - 12:30 PM
    (780, 810)   # 1:00 PM - 1:30 PM
]

megan_blocked = [
    (540, 720),  # 9:00 AM - 12:00 PM
    (810, 960),  # 1:30 PM - 4:00 PM
    (990, 1020)  # 4:30 PM - 5:00 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Virginia's constraints
for s, e in virginia_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Charles's constraints
for s, e in charles_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Megan's constraints
for s, e in megan_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Additional constraints based on preferences and valid time range
constraints.append(t >= 870)  # Charles's preference: t >= 2:30 PM (870 minutes)
constraints.append(540 <= t)   # Start time >= 9:00 AM
constraints.append(t <= 960)   # Start time <= 4:00 PM

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