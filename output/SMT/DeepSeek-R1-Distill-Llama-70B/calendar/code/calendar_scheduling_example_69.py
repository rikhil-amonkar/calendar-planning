from z3 import *

# Blocked intervals in minutes
shirley_blocked = [
    (660, 690),  # 11:00 AM - 11:30 AM
    (840, 900),  # 2:00 PM - 3:00 PM
    (960, 990)   # 4:00 PM - 4:30 PM
]

stephen_blocked = [
    (780, 810),  # 1:00 PM - 1:30 PM
    (930, 960)   # 3:30 PM - 4:00 PM
]

paul_blocked = [
    (540, 600),  # 9:00 AM - 10:00 AM
    (660, 1020)  # 11:00 AM - 5:00 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Shirley's constraints
for s, e in shirley_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Stephen's constraints
for s, e in stephen_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Paul's constraints
for s, e in paul_blocked:
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