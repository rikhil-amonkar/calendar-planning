from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 270)  # Must end by 13:30 (270 minutes)

# Kathryn's blocked times
kathryn_blocks = [(0, 30), (90, 120), (150, 180), (210, 270), (450, 480)]
for start, end in kathryn_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Charlotte's blocked times and preference
charlotte_blocks = [(180, 210), (420, 450)]
for start, end in charlotte_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Lauren's blocked times
lauren_blocks = [(0, 60), (180, 210), (270, 330), (360, 420), (450, 480)]
for start, end in lauren_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")