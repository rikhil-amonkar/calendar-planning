from z3 import *

# Blocked intervals in minutes
jeremy_blocked = [
    (870, 930)  # 14:30-15:30
]

lawrence_blocked = [
    (930, 960),  # 15:30-16:00
    (990, 1020)  # 16:30-17:00
]

helen_blocked = [
    (570, 600),  # 9:30-10:00
    (630, 660),  # 10:30-11:00
    (690, 720),  # 11:30-12:00
    (780, 840),  # 13:00-14:00
    (900, 930),  # 15:00-15:30
    (960, 1020)  # 16:00-17:00
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Jeremy's constraints
for s, e in jeremy_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Lawrence's constraints
for s, e in lawrence_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Helen's constraints
for s, e in helen_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Add constraints for valid time range
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 960)  # 16:00

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