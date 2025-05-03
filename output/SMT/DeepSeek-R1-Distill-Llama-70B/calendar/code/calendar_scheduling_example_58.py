from z3 import *

# Blocked intervals in minutes
joan_blocked = [
    (660, 690),  # 11:00 AM - 11:30 AM
    (750, 780)   # 12:30 PM - 1:00 PM
]

theresa_blocked = [
    (720, 750),  # 12:00 PM - 12:30 PM
    (900, 930)   # 3:00 PM - 3:30 PM
]

shirley_blocked = [
    (570, 630),  # 9:30 AM - 10:30 AM
    (660, 720),  # 11:00 AM - 12:00 PM
    (780, 840),  # 1:00 PM - 2:00 PM
    (930, 990)   # 3:30 PM - 4:30 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Joan's constraints
for s, e in joan_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Theresa's constraints
for s, e in theresa_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Shirley's constraints
for s, e in shirley_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Add constraints for valid time range
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 900)  # 4:00 PM

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