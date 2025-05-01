from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 60 <= 480)  # Work hours constraint (9:00-17:00)

# Kevin's busy blocks: 9:00-10:00 (0-60), 10:30-11:30 (90-150), 12:00-15:30 (180-390), 16:30-17:00 (450-480)
kevin_blocks = [(0, 60), (90, 150), (180, 390), (450, 480)]
for start, end in kevin_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Katherine and Nicole have no constraints

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")