from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 60 <= 480)  # Must end by 17:00 (480 minutes)

# Arthur's blocked times
arthur_blocks = [(0, 30), (90, 180), (420, 480)]
for start, end in arthur_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Michael's blocked times
michael_blocks = [(240, 270), (300, 330)]
for start, end in michael_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Samantha's blocked times
samantha_blocks = [(90, 120), (180, 360), (390, 480)]
for start, end in samantha_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")