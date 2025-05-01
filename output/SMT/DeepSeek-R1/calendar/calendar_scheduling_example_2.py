from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 360)  # Must end by 15:30 (390 minutes = 15:30)

# Roy's blocked times
roy_blocks = [(0, 30), (60, 90), (120, 150), (210, 240)]
for start, end in roy_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Kathryn's blocked times
kathryn_blocks = [(30, 60), (450, 480)]
for start, end in kathryn_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Amy's blocked times and preference
amy_blocks = [(0, 330), (360, 420), (450, 480)]
for start, end in amy_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")