from z3 import *

# Blocked intervals in minutes
eric_blocked = [
    (600, 720)  # 10:00 AM - 12:00 PM
]

albert_blocked = [
    (720, 750),  # 12:00 PM - 12:30 PM
    (930, 960)   # 3:30 PM - 4:00 PM
]

katherine_blocked = [
    (600, 660),  # 10:00 AM - 11:00 AM
    (690, 780),  # 11:30 AM - 2:00 PM
    (900, 930)   # 3:00 PM - 3:30 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Eric's constraints
for s, e in eric_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Albert's constraints
for s, e in albert_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Katherine's constraints
for s, e in katherine_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Add constraints for valid time range, considering Eric's preference
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 810)  # 2:30 PM

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