from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 60 <= 480)  # Work hours constraint (9:00-17:00)

# Stephen's busy blocks: 10:00-10:30 (60-90), 13:00-13:30 (240-270),
# 14:30-15:00 (330-360), 16:00-16:30 (420-450)
stephen_blocks = [(60, 90), (240, 270), (330, 360), (420, 450)]
for start, end in stephen_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Edward's busy blocks: 9:00-9:30 (0-30), 10:00-10:30 (60-90),
# 13:30-14:30 (270-330), 15:00-16:00 (360-420)
edward_blocks = [(0, 30), (60, 90), (270, 330), (360, 420)]
for start, end in edward_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Angela's busy blocks: 9:00-11:30 (0-150), 12:30-13:00 (210-240),
# 13:30-15:30 (270-390), 16:00-17:00 (420-480)
angela_blocks = [(0, 150), (210, 240), (270, 390), (420, 480)]
for start, end in angela_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")