from z3 import *

s = Int('s')
solver = Solver()

# Meeting must fit within work hours (9:00-17:00 = 0-480 minutes)
solver.add(s >= 0)
solver.add(s + 30 <= 480)

# Martha's preference: no meetings before 14:00 (300 minutes from 9:00)
solver.add(s >= 300)

# Richard's busy intervals (minutes from 9:00)
for start, end in [(270, 300), (360, 390)]:
    solver.add(Or(s + 30 <= start, s >= end))

# Martha's busy intervals
for start, end in [(0, 30), (240, 270)]:
    solver.add(Or(s + 30 <= start, s >= end))

# Kimberly's busy intervals
for start, end in [(0, 120), (150, 180), (210, 240), (300, 420)]:
    solver.add(Or(s + 30 <= start, s >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[s].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No solution found")