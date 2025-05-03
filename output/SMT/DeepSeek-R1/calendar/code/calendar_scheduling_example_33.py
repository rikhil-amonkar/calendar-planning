from z3 import *

s = Int('s')
solver = Solver()

# Define work hours constraints (9:00-17:00 = 0-480 minutes)
solver.add(s >= 0)
solver.add(s + 30 <= 480)

# Bobby's preference: meeting ends by 15:00 (360 minutes from 9:00)
solver.add(s + 30 <= 360)

# Lisa's busy intervals (converted to minutes)
for start, end in [(0, 60), (90, 150), (210, 240), (420, 450)]:
    solver.add(Or(s + 30 <= start, s >= end))

# Bobby's busy intervals
for start, end in [(0, 30), (60, 90), (150, 180), (360, 390)]:
    solver.add(Or(s + 30 <= start, s >= end))

# Randy's busy intervals
for start, end in [(30, 60), (90, 120), (150, 210), (240, 270), (330, 390), (420, 450)]:
    solver.add(Or(s + 30 <= start, s >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[s].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No solution found")