from z3 import *

# Blocked intervals in minutes
jeremy_blocked = [
    (720, 780),  # 12:00-1:00 PM
    (810, 840),  # 1:30-2:00 PM
    (900, 930)   # 3:00-3:30 PM
]

donna_blocked = [
    (570, 600),  # 9:30-10:00 AM
    (780, 810),  # 1:00-1:30 PM
    (960, 1020)  # 4:00-5:00 PM
]

robert_blocked = [
    (540, 660),  # 9:00-11:00 AM
    (690, 720),  # 11:30 AM-12:00 PM
    (750, 1020)  # 12:30 PM-5:00 PM
]

t = Int('t')

# Create constraints
constraints = []

# Add constraints for Jeremy
for s, e in jeremy_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Add constraints for Donna
for s, e in donna_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Add constraints for Robert
for s, e in robert_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Add constraints for valid time range
constraints.append(540 <= t)
constraints.append(t <= 960)

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