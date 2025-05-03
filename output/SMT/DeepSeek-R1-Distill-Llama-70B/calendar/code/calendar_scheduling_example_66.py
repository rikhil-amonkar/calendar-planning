from z3 import *

# Blocked intervals in minutes for Charles
charles_blocked = [
    (540, 630),  # 9:00 AM - 10:30 AM
    (660, 690),  # 11:00 AM - 11:30 AM
    (810, 840),  # 1:30 PM - 2:00 PM
    (870, 900),  # 2:30 PM - 3:00 PM
    (930, 990)   # 3:30 PM - 4:30 PM
]

t = Int('t')

# Create constraints for Charles's blocked times
constraints = []

for s, e in charles_blocked:
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