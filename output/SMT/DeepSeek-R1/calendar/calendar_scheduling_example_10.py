from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Total workday constraint (9:00-17:00)

# Janet's preference: meeting must end by 12:00 (180 minutes from 9:00)
solver.add(S + 30 <= 180)

# Diana's blocked times (11:30-12:00, 13:00-13:30 in minutes)
diana_blocks = [(150, 180), (240, 270)]
for start, end in diana_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Ethan has no blocked times (no constraints added)

# Janet's blocked times (9:00-10:00, 12:30-13:00, 14:00-15:00, 15:30-17:00)
janet_blocks = [(0, 60), (210, 240), (300, 360), (390, 480)]
for start, end in janet_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")