from z3 import *

# Blocked intervals in minutes
ronald_blocked = [
    (540, 600),  # 9:00-10:00
    (660, 720)   # 11:00-12:00
]

teresa_blocked = [
    (630, 660),  # 10:30-11:00
    (840, 870)   # 14:00-14:30
]

carol_blocked = [
    (540, 750),  # 9:00-12:30
    (840, 900),  # 14:00-15:30
    (960, 1020)  # 16:00-17:00
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Ronald's constraints
for s, e in ronald_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Teresa's constraints
for s, e in teresa_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Carol's constraints
for s, e in carol_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Add constraints for valid time range
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 1020)  # 5:00 PM

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