from z3 import *

s = Int('s')
solver = Solver()

# Work hours constraints (9:00-17:00 = 0-480 minutes)
solver.add(s >= 0)
solver.add(s + 60 <= 480)

# Ryan's busy intervals (converted to minutes from 9:00)
ryan_busy = [(0, 30), (210, 240)]
for start, end in ryan_busy:
    solver.add(Or(s + 60 <= start, s >= end))

# Denise's preference: meeting ends by 12:30 (210 minutes from 9:00)
solver.add(s + 60 <= 210)

# Denise's busy intervals
denise_busy = [(30, 90), (180, 240), (330, 450)]
for start, end in denise_busy:
    solver.add(Or(s + 60 <= start, s >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[s].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No solution found")