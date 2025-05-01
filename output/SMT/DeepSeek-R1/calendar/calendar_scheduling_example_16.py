from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Work hours constraint (9:00-17:00)

# Scott's blocked times: 9:30-10:30 (30-90), 13:30-14:00 (270-300), 
# 14:30-15:00 (330-360), 15:30-16:00 (390-420), 16:30-17:00 (450-480)
scott_blocks = [(30, 90), (270, 300), (330, 360), (390, 420), (450, 480)]
for start, end in scott_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Christine's blocked times: 9:00-10:00 (0-60), 10:30-12:30 (90-210), 13:00-17:00 (240-480)
christine_blocks = [(0, 60), (90, 210), (240, 480)]
for start, end in christine_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")