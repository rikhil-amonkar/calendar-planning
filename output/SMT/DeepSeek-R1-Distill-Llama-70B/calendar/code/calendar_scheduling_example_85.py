from z3 import *

# Blocked intervals in minutes
julia_blocked = [
    (570, 600),  # 9:30-10:00
    (840, 870),  # 14:00-14:30
    (900, 930),  # 15:00-15:30
    (990, 1020)  # 16:30-17:00
]

martha_blocked = [
    (540, 660),  # 9:00-11:00
    (720, 900)   # 12:00-15:00
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Julia's constraints
for s, e in julia_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Martha's constraints
for s, e in martha_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Add constraints for valid time range, considering Julia's preference
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 780)  # 13:00

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