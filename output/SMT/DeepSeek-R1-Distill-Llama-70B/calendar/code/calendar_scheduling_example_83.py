from z3 import *

# Blocked intervals in minutes
anthony_blocked = [
    (840, 870),  # 14:00-14:30
    (900, 930)   # 15:00-15:30
]

ronald_blocked = [
    (540, 600),  # 9:00-10:00
    (720, 750),  # 12:00-12:30
    (810, 840)   # 13:30-14:00
]

jonathan_blocked = [
    (540, 600),  # 9:00-10:00
    (660, 690),  # 11:00-11:30
    (720, 780),  # 12:00-13:00
    (840, 870),  # 14:00-14:30
    (900, 1020)  # 15:00-17:00
]

t = Int('t')

# Create constraints for each person's blocked times
constraints = []

# Anthony's constraints
for s, e in anthony_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Ronald's constraints
for s, e in ronald_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Jonathan's constraints
for s, e in jonathan_blocked:
    constraints.append(Or(t + 60 <= s, t >= e))

# Add constraints for valid time range
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 1020)  # 5:00 PM

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