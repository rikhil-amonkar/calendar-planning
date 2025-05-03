from z3 import *

# Blocked intervals in minutes
michael_blocked = [
    (570, 630),  # 9:30-10:30
    (900, 930),  # 15:00-15:30
    (960, 990)   # 16:00-16:30
]

arthur_blocked = [
    (540, 720),  # 9:00-12:00
    (780, 900),  # 13:00-15:00
    (930, 960),  # 15:30-16:00
    (990, 1020)  # 16:30-17:00
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Michael's constraints
for s, e in michael_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Arthur's constraints
for s, e in arthur_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

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