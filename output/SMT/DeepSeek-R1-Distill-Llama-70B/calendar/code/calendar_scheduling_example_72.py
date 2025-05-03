from z3 import *

# Blocked intervals in minutes
amy_blocked = [
    (570, 690),  # 9:30 AM - 11:30 AM
    (780, 810),  # 1:00 PM - 1:30 PM
    (990, 1020)  # 4:30 PM - 5:00 PM
]

christopher_blocked = [
    (540, 600),  # 9:00 AM - 10:00 AM
    (720, 810),  # 12:00 PM - 1:30 PM
    (870, 900),  # 2:30 PM - 3:00 PM
    (990, 1020)  # 4:30 PM - 5:00 PM
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Amy's constraints
for s, e in amy_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Christopher's constraints
for s, e in christopher_blocked:
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