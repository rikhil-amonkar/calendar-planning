from z3 import *

# Blocked intervals in minutes
lisa_blocked = [
    (630, 660),  # 10:30 AM - 11:00 AM
    (690, 720),  # 11:30 AM - 12:00 PM
    (840, 900)   # 2:00 PM - 3:00 PM
]

raymond_blocked = [
    (540, 600),  # 9:00 AM - 10:00 AM
    (630, 660),  # 10:30 AM - 11:00 AM
    (690, 900),  # 11:30 AM - 3:00 PM
    (960, 1020)  # 4:00 PM - 5:00 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Lisa's constraints
for s, e in lisa_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Raymond's constraints
for s, e in raymond_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Additional constraints based on preferences and valid time range
constraints.append(t >= 540)  # Start time >= 9:00 AM
constraints.append(t <= 960)  # Start time <= 4:00 PM
constraints.append(t <= 630)  # Dorothy's preference: t <= 10:30 AM

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