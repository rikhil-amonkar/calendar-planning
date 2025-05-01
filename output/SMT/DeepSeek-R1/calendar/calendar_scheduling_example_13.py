from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Total workday constraint (9:00-17:00)

# Gerald's constraints
# Blocked times: 9:00-9:30 (0-30), 13:00-14:00 (240-300), 15:00-15:30 (360-390), 16:00-17:00 (420-480)
gerald_blocks = [(0, 30), (240, 300), (360, 390), (420, 480)]
for start, end in gerald_blocks:
    solver.add(Or(S + 30 <= start, S >= end))
# Prefers to avoid before 13:00 (240 minutes from 9:00)
solver.add(S >= 240)

# Barbara's blocked times: 9:30-10:00 (30-60), 11:30-14:00 (150-300), 14:30-15:00 (330-360), 15:30-17:00 (390-480)
barbara_blocks = [(30, 60), (150, 300), (330, 360), (390, 480)]
for start, end in barbara_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Roy has no constraints

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")