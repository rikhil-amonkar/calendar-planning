from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Work hours constraint (9:00-17:00)

# Billy's preference: meeting must end by 15:30 (390 minutes from 9:00)
solver.add(S + 30 <= 390)

# Patricia's blocked times: 9:00-12:30 (0-210), 13:30-14:00 (270-300),
# 14:30-16:00 (330-420), 16:30-17:00 (450-480)
patricia_blocks = [(0, 210), (270, 300), (330, 420), (450, 480)]
for start, end in patricia_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Billy's blocked times: 10:00-10:30 (60-90), 11:30-12:00 (150-180),
# 14:00-14:30 (300-330), 16:30-17:00 (450-480)
billy_blocks = [(60, 90), (150, 180), (300, 330), (450, 480)]
for start, end in billy_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Brian has no constraints

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")