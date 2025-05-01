from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Total workday constraint (9:00-17:00)

# Diane's blocked times (9:00-9:30, 12:00-12:30, 14:30-15:30)
diane_blocks = [(0, 30), (180, 210), (330, 390)]
for start, end in diane_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Kelly's blocked times (9:30-10:00, 10:30-11:00)
kelly_blocks = [(30, 60), (90, 120)]
for start, end in kelly_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Deborah's blocked times (9:00-9:30, 10:00-14:00, 14:30-17:00)
deborah_blocks = [(0, 30), (60, 300), (330, 480)]
for start, end in deborah_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")