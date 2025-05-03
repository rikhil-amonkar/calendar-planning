from z3 import *

# Blocked intervals in minutes
jack_blocked = [
    (630, 690),  # 10:30 AM - 11:30 AM
    (780, 810),  # 1:00 PM - 1:30 PM
    (840, 870),  # 2:00 PM - 2:30 PM
    (960, 1020)  # 4:00 PM - 5:00 PM
]

judith_blocked = [
    (540, 600),   # 9:00 AM - 10:00 AM
    (630, 660),   # 10:30 AM - 11:00 AM
    (690, 840),   # 11:30 AM - 2:00 PM
    (870, 900),   # 2:30 PM - 3:00 PM
    (930, 1020)   # 3:30 PM - 5:00 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Jack's constraints
for s, e in jack_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Judith's constraints
for s, e in judith_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Additional constraints based on preferences and valid time range
constraints.append(t >= 840)  # Jeffrey's preference: t >= 2:00 PM (840 minutes)
constraints.append(t >= 540)  # Start time >= 9:00 AM
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