from z3 import *

# Blocked intervals in minutes
beverly_blocked = [
    (570, 600),  # 9:30 AM - 10:00 AM
    (660, 690),  # 11:00 AM - 11:30 AM
    (750, 780),  # 12:30 PM - 1:00 PM
    (840, 870),  # 2:00 PM - 2:30 PM
    (930, 960),  # 3:30 PM - 4:00 PM
    (990, 1020)  # 4:30 PM - 5:00 PM
]

peter_blocked = [
    (570, 630),  # 9:30 AM - 10:30 AM
    (690, 780),  # 11:30 AM - 1:00 PM
    (870, 930),  # 2:30 PM - 3:30 PM
    (990, 1020)  # 4:30 PM - 5:00 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Beverly's constraints
for s, e in beverly_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Peter's constraints
for s, e in peter_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Add constraints for valid time range
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 960)  # 4:00 PM

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