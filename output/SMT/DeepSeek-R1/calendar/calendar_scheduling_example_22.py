from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 60 <= 480)  # Work hours constraint (9:00-17:00)

# Theresa's busy blocks: 9:00-9:30 (0-30), 12:30-13:30 (210-270), 14:00-15:00 (300-360), 16:30-17:00 (450-480)
theresa_blocks = [(0, 30), (210, 270), (300, 360), (450, 480)]
for start, end in theresa_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Charles's busy blocks: 10:00-10:30 (60-90), 11:30-12:30 (150-210), 14:00-15:30 (300-390)
charles_blocks = [(60, 90), (150, 210), (300, 390)]
for start, end in charles_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Betty's busy blocks: 9:00-10:30 (0-90), 12:00-12:30 (180-210), 13:00-14:00 (240-300), 15:00-16:00 (360-420)
betty_blocks = [(0, 90), (180, 210), (240, 300), (360, 420)]
for start, end in betty_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")