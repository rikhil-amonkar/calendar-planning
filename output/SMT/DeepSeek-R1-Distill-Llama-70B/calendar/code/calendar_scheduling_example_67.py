from z3 import *

# Blocked intervals in minutes
jacqueline_blocked = [
    (780, 810),  # 13:00-13:30
    (960, 990)   # 16:00-16:30
]

linda_blocked = [
    (540, 630),  # 9:00-10:30
    (690, 750),  # 11:30-12:30
    (840, 870),  # 14:00-14:30
    (930, 990)   # 15:30-16:30
]

t = Int('t')

# Create constraints for Jacqueline's blocked times
constraints = []
for s, e in jacqueline_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Create constraints for Linda's blocked times
for s, e in linda_blocked:
    constraints.append(Or(t + 30 <= s, t >= e))

# Add constraints for valid time range, considering Linda's preference
constraints.append(540 <= t)  # 9:00 AM
constraints.append(t <= 810)  # 13:30

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