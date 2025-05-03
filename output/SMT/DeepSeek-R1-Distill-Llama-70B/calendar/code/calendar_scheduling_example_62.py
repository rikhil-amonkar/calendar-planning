from z3 import *

# Blocked intervals in minutes
sharon_blocked = [
    (540, 780),  # 9:00 AM - 1:00 PM
    (840, 1020)  # 2:00 PM - 5:00 PM
]

t = Int('t')

# Create constraints for Sharon's blocked times
constraints = []

# Sharon's constraints
for s, e in sharon_blocked:
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