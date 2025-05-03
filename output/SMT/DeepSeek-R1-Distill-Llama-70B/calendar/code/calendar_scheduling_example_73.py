from z3 import *

# Blocked intervals in minutes
bradley_blocked = [
    (570, 600),  # 9:30 AM - 10:00 AM
    (780, 810),  # 1:00 PM - 1:30 PM
    (870, 900),  # 2:30 PM - 3:00 PM
    (990, 1020)  # 4:30 PM - 5:00 PM
]

andrew_blocked = [
    (540, 570),  # 9:00 AM - 9:30 AM
    (750, 810),  # 12:30 PM - 1:30 PM
    (840, 870),  # 2:00 PM - 2:30 PM
    (900, 960)   # 3:00 PM - 4:00 PM
]

melissa_blocked = [
    (540, 570),  # 9:00 AM - 9:30 AM
    (600, 630),  # 10:00 AM - 10:30 AM
    (660, 840),  # 11:00 AM - 2:00 PM
    (900, 930),  # 3:00 PM - 3:30 PM
    (960, 990)   # 4:00 PM - 4:30 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Bradley's constraints
for s, e in bradley_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Andrew's constraints
for s, e in andrew_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Melissa's constraints
for s, e in melissa_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

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