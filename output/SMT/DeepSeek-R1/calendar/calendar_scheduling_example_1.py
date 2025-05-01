from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 360)  # Must end by 15:00 (360 minutes = 15:00)

# Raymond's blocked times
raymond_blocks = [(0, 30), (150, 180), (240, 270), (360, 390)]
for start, end in raymond_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Billy's blocked times and preference (ends by 15:00 handled above)
billy_blocks = [(60, 90), (180, 240), (450, 480)]
for start, end in billy_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Donald's blocked times
donald_blocks = [(0, 30), (60, 120), (180, 240), (300, 330), (420, 480)]
for start, end in donald_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")