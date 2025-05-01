from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Work hours constraint (9:00-17:00)

# Christine's constraint: cannot meet before 12:00 (180 minutes from 9:00)
solver.add(S >= 180)

# Joyce's blocked times: 11:00-11:30 (120-150), 13:30-14:00 (270-300), 14:30-16:30 (330-450)
joyce_blocks = [(120, 150), (270, 300), (330, 450)]
for start, end in joyce_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Alexander's blocked times: 9:00-11:00 (0-120), 12:00-12:30 (180-210), 13:30-15:00 (270-360), 
# 15:30-16:00 (390-420), 16:30-17:00 (450-480)
alex_blocks = [(0, 120), (180, 210), (270, 360), (390, 420), (450, 480)]
for start, end in alex_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")