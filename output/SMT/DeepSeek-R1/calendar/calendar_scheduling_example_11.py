from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Total workday constraint (9:00-17:00)

# Alexander's blocked times (9:30-10:00, 10:30-11:00, 12:30-13:00, 14:30-15:00, 16:00-17:00)
alexander_blocks = [(30, 60), (90, 120), (210, 240), (330, 360), (420, 480)]
for start, end in alexander_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Elizabeth's blocked times (9:00-9:30, 11:30-12:30, 13:00-14:30)
elizabeth_blocks = [(0, 30), (150, 180), (240, 330)]
for start, end in elizabeth_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Walter's blocked times (9:00-14:30, 15:30-17:00)
walter_blocks = [(0, 330), (390, 480)]
for start, end in walter_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")