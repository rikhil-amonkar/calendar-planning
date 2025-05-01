from z3 import *

solver = Optimize()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Work hours constraint (9:00-17:00)

# Jesse's busy blocks: 10:00-10:30 (60-90), 15:30-16:00 (390-420)
jesse_blocks = [(60, 90), (390, 420)]
for start, end in jesse_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Megan's busy blocks: 10:30-11:00 (90-120), 11:30-12:30 (150-210), 13:30-14:30 (270-330), 15:00-16:30 (360-450)
megan_blocks = [(90, 120), (150, 210), (270, 330), (360, 450)]
for start, end in megan_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Kathryn has no constraints

# Find earliest possible time
solver.minimize(S)

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")