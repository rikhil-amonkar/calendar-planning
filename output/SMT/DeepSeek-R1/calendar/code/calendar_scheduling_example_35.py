from z3 import *

s = Int('s')
solver = Solver()

# Work hours constraints (9:00-17:00 = 0-480 minutes)
solver.add(s >= 0)
solver.add(s + 30 <= 480)

# Bradley's preference: no meetings before 14:30 (330 minutes)
solver.add(s >= 330)

# Zachary's busy intervals (minutes from 9:00)
for start, end in [(60, 90), (360, 390)]:
    solver.add(Or(s + 30 <= start, s >= end))

# Teresa's busy intervals
for start, end in [(0, 90), (120, 210), (240, 300), (330, 450)]:
    solver.add(Or(s + 30 <= start, s >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[s].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No solution found")