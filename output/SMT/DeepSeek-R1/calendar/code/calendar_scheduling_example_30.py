from z3 import *

s = Int('s')
solver = Solver()

# Define constraints for the meeting time
solver.add(s >= 0)  # Meeting can't start before 9:00
solver.add(s + 30 <= 300)  # Melissa's preference: meeting ends by 14:00 (300 minutes after 9:00)

# Jeffrey's busy intervals (in minutes since 9:00)
for start, end in [(30, 60), (90, 120)]:
    solver.add(Or(s + 30 <= start, s >= end))

# Virginia's busy intervals
for start, end in [(0, 30), (60, 90), (330, 360), (420, 450)]:
    solver.add(Or(s + 30 <= start, s >= end))

# Melissa's busy intervals
for start, end in [(0, 150), (180, 210), (240, 360), (420, 480)]:
    solver.add(Or(s + 30 <= start, s >= end))

if solver.check() == sat:
    m = solver.model()
    start_time = m[s].as_long()
    hours = start_time // 60
    minutes = start_time % 60
    print(f"Meeting starts at {9 + hours}:{minutes:02d}")
else:
    print("No solution found")