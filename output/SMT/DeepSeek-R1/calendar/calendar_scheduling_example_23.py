from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 60 <= 480)  # Work hours constraint (9:00-17:00)

# Billy's busy blocks: 11:30-12:00 (150-180), 13:00-15:00 (240-360), 16:00-16:30 (420-450)
billy_blocks = [(150, 180), (240, 360), (420, 450)]
for start, end in billy_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Maria's busy blocks: 9:00-9:30 (0-30), 10:00-10:30 (60-90), 13:00-13:30 (240-270), 14:00-14:30 (300-330)
maria_blocks = [(0, 30), (60, 90), (240, 270), (300, 330)]
for start, end in maria_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# William's busy blocks: 9:30-10:00 (30-60), 12:00-12:30 (180-210), 13:30-15:00 (270-360), 15:30-17:00 (390-480)
william_blocks = [(30, 60), (180, 210), (270, 360), (390, 480)]
for start, end in william_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")