from z3 import *

# Blocked intervals in minutes
denise_blocked = [
    (720, 750),  # 12:00 PM - 12:30 PM
    (930, 960)   # 3:30 PM - 4:00 PM
]

natalie_blocked = [
    (540, 690),  # 9:00 AM - 11:30 AM
    (720, 780),  # 12:00 PM - 1:00 PM
    (840, 870),  # 2:00 PM - 2:30 PM
    (900, 1020)  # 3:00 PM - 5:00 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Denise's constraints
for s, e in denise_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Natalie's constraints
for s, e in natalie_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Add constraints for valid time range
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 990)  # 4:30 PM

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