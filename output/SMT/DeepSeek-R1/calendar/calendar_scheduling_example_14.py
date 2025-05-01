from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Work hours constraint (9:00-17:00)

# Brandon's constraints
# Blocked times: 13:00-14:00 (240-300), 15:30-16:00 (390-420), 16:30-17:00 (450-480)
brandon_blocks = [(240, 300), (390, 420), (450, 480)]
for start, end in brandon_blocks:
    solver.add(Or(S + 30 <= start, S >= end))
# Prefers to avoid before 14:30 (330 minutes from 9:00)
solver.add(S >= 330)

# Bradley's blocked times: 9:00-11:30 (0-150), 12:00-15:00 (180-360), 16:00-16:30 (420-450)
bradley_blocks = [(0, 150), (180, 360), (420, 450)]
for start, end in bradley_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Jerry has no constraints

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")