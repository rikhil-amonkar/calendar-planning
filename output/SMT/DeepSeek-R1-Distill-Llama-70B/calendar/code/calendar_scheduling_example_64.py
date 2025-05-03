from z3 import *

# Blocked intervals in minutes
nancy_blocked = [
    (570, 600),  # 9:30 AM - 10:00 AM
    (750, 780)   # 12:30 PM - 1:00 PM
]

nathan_blocked = [
    (540, 750),  # 9:00 AM - 12:30 PM
    (780, 870),  # 1:00 PM - 2:30 PM
    (960, 1020)  # 4:00 PM - 5:00 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Nancy's constraints
for s, e in nancy_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Nathan's constraints
for s, e in nathan_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Add constraints for valid time range
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 900)  # 3:00 PM

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