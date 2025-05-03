from z3 import *

s = Int('s')
solver = Solver()

# Meeting must fit within work hours (9:00-17:00 = 0-480 minutes)
solver.add(s >= 0)
solver.add(s + 30 <= 480)

# Frank's preference: no meetings after 9:30 (ends by 9:30 = 30 minutes)
solver.add(s + 30 <= 30)

# Emily's busy intervals (minutes from 9:00)
for start, end in [(60, 90), (150, 180), (300, 360), (420, 450)]:
    solver.add(Or(s + 30 <= start, s >= end))

# Melissa's busy intervals
for start, end in [(30, 60), (330, 360)]:
    solver.add(Or(s + 30 <= start, s >= end))

# Frank's busy intervals
for start, end in [(60, 90), (120, 150), (210, 240), (270, 330), (360, 420), (450, 480)]:
    solver.add(Or(s + 30 <= start, s >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[s].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No solution found")