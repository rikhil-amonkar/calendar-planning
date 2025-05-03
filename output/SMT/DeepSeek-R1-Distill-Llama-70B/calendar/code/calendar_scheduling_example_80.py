from z3 import *

# Blocked intervals in minutes
michelle_blocked = [
    (570, 600),  # 9:30-10:00
    (750, 780)   # 12:30-13:00
]

billy_blocked = [
    (630, 660),  # 10:30-11:00
    (690, 720),  # 11:30-12:00
    (870, 900),  # 14:30-15:00
    (960, 990)   # 16:00-16:30
]

alexis_blocked = [
    (570, 630),  # 9:30-10:30
    (660, 720),  # 11:00-12:00
    (750, 780),  # 12:30-13:00
    (810, 870),  # 13:30-14:30
    (960, 990)   # 16:00-16:30
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Michelle's constraints
for s, e in michelle_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Billy's constraints
for s, e in billy_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Alexis's constraints
for s, e in alexis_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Add constraints for valid time range, considering Alexis's preference
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 900)  # 15:00

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