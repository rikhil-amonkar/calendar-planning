from z3 import *

# Blocked intervals in minutes
jacob_blocked = [
    (540, 570),  # 9:00 AM - 9:30 AM
    (750, 780),  # 12:30 PM - 1:00 PM
    (870, 900),  # 2:30 PM - 3:00 PM
    (990, 1020)  # 4:30 PM - 5:00 PM
]

amanda_blocked = [
    (600, 630),  # 10:00 AM - 10:30 AM
    (720, 750)   # 12:00 PM - 12:30 PM
]

lisa_blocked = [
    (660, 780),  # 11:00 AM - 1:00 PM
    (870, 990)   # 2:30 PM - 4:30 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Jacob's constraints
for s, e in jacob_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Amanda's constraints
for s, e in amanda_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Lisa's constraints
for s, e in lisa_blocked:
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