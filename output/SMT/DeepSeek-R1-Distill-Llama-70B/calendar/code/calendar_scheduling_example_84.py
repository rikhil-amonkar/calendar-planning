from z3 import *

# Blocked intervals in minutes
kevin_blocked = [
    (570, 600),  # 9:30-10:00
    (630, 660),  # 10:30-11:00
    (900, 960)   # 15:00-16:00
]

ryan_blocked = [
    (630, 690),  # 10:30-11:30
    (750, 780),  # 12:30-13:00
    (810, 840)   # 13:30-14:00
]

eugene_blocked = [
    (540, 570),  # 9:00-9:30
    (600, 660),  # 10:00-11:00
    (750, 1020)  # 12:30-17:00
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Kevin's constraints
for s, e in kevin_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Ryan's constraints
for s, e in ryan_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Eugene's constraints
for s, e in eugene_blocked:
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