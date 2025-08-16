from z3 import *

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()

start_min = Int('start_min')

solver.add(start_min >= 540)
solver.add(start_min + 30 <= 1020)

# Patrick's intervals
for s, e in [(810, 840), (870, 900)]:
    solver.add(Or(start_min + 30 <= s, start_min >= e))

# Shirley's intervals
for s, e in [(540, 570), (660, 690), (720, 750), (870, 900), (960, 1020)]:
    solver.add(Or(start_min + 30 <= s, start_min >= e))

# Jeffrey's intervals
for s, e in [(540, 570), (630, 660), (690, 720), (780, 810), (960, 1020)]:
    solver.add(Or(start_min + 30 <= s, start_min >= e))

# Gloria's intervals
for s, e in [(690, 720), (900, 930)]:
    solver.add(Or(start_min + 30 <= s, start_min >= e))

# Nathan's intervals
for s, e in [(540, 570), (630, 720), (840, 1020)]:
    solver.add(Or(start_min + 30 <= s, start_min >= e))

# Angela's intervals
for s, e in [(540, 570), (600, 660), (750, 900), (930, 990)]:
    solver.add(Or(start_min + 30 <= s, start_min >= e))

# David's intervals
for s, e in [(540, 570), (600, 630), (660, 840), (870, 990)]:
    solver.add(Or(start_min + 30 <= s, start_min >= e))

if solver.check() == sat:
    model = solver.model()
    start = model[start_min].as_long()
    end = start + 30
    day = "Monday"
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {minutes_to_time(start)}")
    print(f"End Time: {minutes_to_time(end)}")
else:
    print("No solution found.")