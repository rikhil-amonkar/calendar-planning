from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 60 <= 480)  # Work hours constraint (9:00-17:00)

# Anthony's busy blocks: 9:30-10:00 (30-60), 12:00-13:00 (180-240), 16:00-16:30 (420-450)
anthony_blocks = [(30, 60), (180, 240), (420, 450)]
for start, end in anthony_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Pamela's busy blocks: 9:30-10:00 (30-60), 16:30-17:00 (450-480)
pamela_blocks = [(30, 60), (450, 480)]
for start, end in pamela_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Pamela's preference: meeting must end by 14:30 (330 minutes from 9:00)
solver.add(S + 60 <= 330)

# Zachary's busy blocks: 9:00-11:30 (0-150), 12:00-12:30 (180-210), 13:00-13:30 (240-270), 14:30-15:00 (330-360), 16:00-17:00 (420-480)
zachary_blocks = [(0, 150), (180, 210), (240, 270), (330, 360), (420, 480)]
for start, end in zachary_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")