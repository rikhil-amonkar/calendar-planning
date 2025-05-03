from z3 import *

s = Int('s')
solver = Solver()

# Work hours constraints (9:00-17:00 = 0-480 minutes)
solver.add(s >= 0)
solver.add(s + 30 <= 480)

# Catherine's busy intervals (converted to minutes from 9:00)
catherine_busy = [(90, 120), (210, 270), (330, 360)]
for start, end in catherine_busy:
    solver.add(Or(s + 30 <= start, s >= end))

# Michael's busy intervals
michael_busy = [(30, 90), (180, 240), (270, 300), (360, 390)]
for start, end in michael_busy:
    solver.add(Or(s + 30 <= start, s >= end))

# Alexander's busy intervals
alexander_busy = [(0, 30), (60, 90), (120, 180), (240, 270), (300, 420), (450, 480)]
for start, end in alexander_busy:
    solver.add(Or(s + 30 <= start, s >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[s].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No solution found")