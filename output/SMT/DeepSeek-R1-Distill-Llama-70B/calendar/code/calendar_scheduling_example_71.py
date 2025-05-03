from z3 import *

# Blocked intervals in minutes
john_blocked = [
    (750, 780)  # 12:30 PM - 1:00 PM
]

ethan_blocked = [
    (540, 600),  # 9:00 AM - 10:00 AM
    (690, 840),  # 11:30 AM - 2:00 PM
    (870, 1020)  # 2:30 PM - 5:00 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# John's constraints
for s, e in john_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Ethan's constraints
for s, e in ethan_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Add constraints for valid time range, considering John's preference
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