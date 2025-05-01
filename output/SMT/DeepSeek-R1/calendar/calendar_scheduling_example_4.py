from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Must end by 17:00 (480 minutes)

# Donna's blocked times
donna_blocks = [(300, 330), (390, 420)]
for start, end in donna_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# John's blocked times
john_blocks = [(120, 150), (450, 480)]
for start, end in john_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Billy's blocked times
billy_blocks = [(0, 60), (90, 300), (330, 480)]
for start, end in billy_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")