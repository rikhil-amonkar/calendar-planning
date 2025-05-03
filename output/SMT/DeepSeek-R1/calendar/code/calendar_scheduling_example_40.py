from z3 import *

s = Int('s')
solver = Solver()

# Work hours constraints (9:00-17:00 = 0-480 minutes)
solver.add(s >= 0)
solver.add(s + 60 <= 480)

# Jacob's busy intervals (converted to minutes from 9:00)
jacob_busy = [(60, 120), (150, 180), (420, 450)]
for start, end in jacob_busy:
    solver.add(Or(s + 60 <= start, s >= end))

# Gabriel's busy intervals
gabriel_busy = [(30, 150), (240, 270), (360, 390)]
for start, end in gabriel_busy:
    solver.add(Or(s + 60 <= start, s >= end))

# Matthew's busy intervals
matthew_busy = [(0, 30), (90, 120), (150, 180), (210, 300), (390, 450)]
for start, end in matthew_busy:
    solver.add(Or(s + 60 <= start, s >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[s].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No solution found")