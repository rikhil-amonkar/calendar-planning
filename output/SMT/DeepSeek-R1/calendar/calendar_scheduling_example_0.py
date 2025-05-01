from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S <= 420)  # 420 minutes = 16:00 (meeting ends by 17:00)

# Michelle's blocked time: 11:00-12:00 (120-180 minutes)
solver.add(Or(S + 60 <= 120, S >= 180))

# Steven's blocked times
steven_blocks = [(0, 30), (150, 180), (270, 300), (390, 420)]
for start, end in steven_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Jerry's blocked times
jerry_blocks = [(0, 30), (60, 120), (150, 210), (240, 330), (390, 420), (450, 480)]
for start, end in jerry_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")