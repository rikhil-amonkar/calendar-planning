from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 60 <= 480)  # Total workday constraint (9:00-17:00)

# Debra's blocked times (9:30-10:00, 11:00-11:30, 12:00-13:00, 14:00-14:30, 16:00-16:30)
debra_blocks = [(30, 60), (120, 150), (180, 240), (300, 330), (420, 450)]
for start, end in debra_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Kevin's blocked times (9:00-12:00, 14:00-17:00)
kevin_blocks = [(0, 180), (300, 480)]
for start, end in kevin_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# David has no blocked times (no constraints added)

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")