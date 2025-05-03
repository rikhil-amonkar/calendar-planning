from z3 import *

solver = Solver()
S = Int('S')

# Define the start time within work hours (9:00 to 17:00) and ensure the meeting ends by 16:30 for Andrea
solver.add(S >= 0, S + 30 <= 450)  # 450 minutes = 16:30 (9:00 + 7h30m)

# John's busy intervals (in minutes since 9:00)
john_busy = [(210, 240), (390, 420)]  # 12:30-13:00, 15:30-16:00
for start, end in john_busy:
    solver.add(Or(S + 30 <= start, S >= end))

# Andrea's busy intervals and constraints
andrea_busy = [(0, 30), (120, 210), (360, 390), (420, 450)]  # 9:00-9:30, 11:00-12:30, 15:00-15:30, 16:00-16:30
for start, end in andrea_busy:
    solver.add(Or(S + 30 <= start, S >= end))

# Lisa's busy intervals
lisa_busy = [(0, 60), (90, 120), (180, 210), (300, 390), (420, 450)]  # 9:00-10:00, 10:30-11:00, 12:00-12:30, 14:00-15:30, 16:00-16:30
for start, end in lisa_busy:
    solver.add(Or(S + 30 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    h = 9 + start_min // 60
    m = start_min % 60
    print(f"Meeting starts at {h:02d}:{m:02d}")
else:
    print("No valid time found")