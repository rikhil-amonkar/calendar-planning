from z3 import *

# Blocked intervals in minutes
donald_blocked = [
    (600, 630),  # 10:00-10:30
    (660, 690),  # 11:00-11:30
    (720, 750),  # 12:00-12:30
    (780, 810),  # 13:00-13:30
    (930, 990)   # 15:30-16:30
]

joyce_blocked = [
    (660, 780),  # 11:00-13:00
    (870, 900),  # 14:30-15:00
    (960, 990)   # 16:00-16:30
]

abigail_blocked = [
    (570, 600),  # 9:30-10:00
    (690, 720),  # 11:30-12:00
    (780, 840),  # 13:00-14:00
    (900, 1020)  # 15:00-17:00
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Donald's constraints
for s, e in donald_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Joyce's constraints
for s, e in joyce_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Abigail's constraints
for s, e in abigail_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Add constraints for valid time range, considering Donald's preference
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 720)  # 12:00 PM

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