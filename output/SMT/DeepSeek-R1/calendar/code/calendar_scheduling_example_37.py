from z3 import *

s = Int('s')
solver = Solver()

# Work hours constraints (9:00-17:00 = 0-480 minutes)
solver.add(s >= 0)
solver.add(s + 30 <= 480)

# Gregory's busy intervals (converted to minutes from 9:00)
gregory_busy = [(120, 150), (180, 210), (390, 450)]
for start, end in gregory_busy:
    solver.add(Or(s + 30 <= start, s >= end))

# Carol's busy intervals
carol_busy = [(0, 90), (120, 420), (450, 480)]
for start, end in carol_busy:
    solver.add(Or(s + 30 <= start, s >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[s].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No solution found")