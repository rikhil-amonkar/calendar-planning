from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 60 <= 480)  # Total workday constraint (9:00-17:00)

# Dylan's blocked times (10:30-11:00 and 13:30-14:00)
dylan_blocks = [(90, 120), (270, 300)]
for start, end in dylan_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Jerry's blocked times (9:00-11:00, 11:30-14:30, 16:00-17:00)
solver.add(S >= 120)  # Must start after 11:00 (first available gap)
solver.add(Or(S + 60 <= 150, S >= 330))  # Avoid 11:30-14:30 block
solver.add(S + 60 <= 420)  # Must end before 16:00

# Thomas has no constraints

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")