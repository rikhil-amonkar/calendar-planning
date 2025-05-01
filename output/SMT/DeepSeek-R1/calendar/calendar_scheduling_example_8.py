from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Total workday constraint (9:00-17:00)

# Adam's blocked times (10:00-10:30, 12:30-13:00, 13:30-14:30)
adam_blocks = [(60, 90), (210, 240), (270, 330)]
for start, end in adam_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Jerry's blocked times (9:00-9:30, 12:00-12:30, 15:00-16:00)
jerry_blocks = [(0, 30), (180, 210), (360, 420)]
for start, end in jerry_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Matthew's blocked times (9:30-11:00, 11:30-12:30, 13:00-14:00, 14:30-17:00)
matthew_blocks = [(30, 120), (150, 180), (240, 300), (330, 480)]
for start, end in matthew_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")