from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Total workday constraint (9:00-17:00)

# Heather's blocked times (9:00-9:30, 10:30-11:00, 13:00-14:00, 14:30-15:00, 16:00-16:30)
heather_blocks = [(0, 30), (90, 120), (240, 300), (330, 360), (420, 450)]
for start, end in heather_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Zachary's blocked times (9:00-10:30, 11:00-12:00, 12:30-13:00, 13:30-16:30)
zachary_blocks = [(0, 90), (120, 180), (210, 240), (270, 450)]
for start, end in zachary_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Zachary's preference: meeting ends by 14:00 (300 minutes from 9:00)
solver.add(S + 30 <= 300)

# Nicholas has no constraints

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")