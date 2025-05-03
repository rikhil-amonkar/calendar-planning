from z3 import *

s = Int('s')
solver = Solver()

# Work hours constraints (9:00-17:00 = 0-480 minutes)
solver.add(s >= 0)
solver.add(s + 60 <= 480)

# Richard's busy intervals (converted to minutes from 9:00)
richard_busy = [(60, 90), (120, 180), (240, 300), (420, 450)]
for start, end in richard_busy:
    solver.add(Or(s + 60 <= start, s >= end))

# Noah's busy intervals
noah_busy = [(60, 90), (150, 240), (270, 300), (330, 480)]
for start, end in noah_busy:
    solver.add(Or(s + 60 <= start, s >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[s].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No solution found")