from z3 import *

# Blocked intervals in minutes
amy_blocked = [
    (660, 690),  # 11:00 AM - 11:30 AM
    (720, 750)   # 12:00 PM - 12:30 PM
]

john_blocked = [
    (600, 630),  # 10:00 AM - 10:30 AM
    (690, 720),  # 11:30 AM - 12:00 PM
    (750, 960),  # 12:30 PM - 4:00 PM
    (990, 1020)  # 4:30 PM - 5:00 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Amy's constraints
for s, e in amy_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# John's constraints
for s, e in john_blocked:
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