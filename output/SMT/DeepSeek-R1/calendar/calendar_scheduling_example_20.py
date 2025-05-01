from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Work hours constraint (9:00-17:00)

# Daniel's preference: meeting must end by 13:30 (270 minutes from 9:00)
solver.add(S + 30 <= 270)

# Ralph's busy blocks: 13:30-14:00 (270-300), 14:30-15:00 (330-360)
ralph_blocks = [(270, 300), (330, 360)]
for start, end in ralph_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Peter's busy blocks: 9:00-9:30 (0-30), 11:00-13:00 (120-240), 16:00-16:30 (420-450)
peter_blocks = [(0, 30), (120, 240), (420, 450)]
for start, end in peter_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Daniel's blocked calendar: 9:00-10:00 (0-60), 10:30-15:30 (90-390), 16:00-17:00 (420-480)
daniel_blocks = [(0, 60), (90, 390), (420, 480)]
for start, end in daniel_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")