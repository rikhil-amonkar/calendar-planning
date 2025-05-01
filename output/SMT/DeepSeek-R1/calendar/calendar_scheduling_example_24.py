from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Work hours constraint (9:00-17:00)

# Benjamin's constraint: meeting must end by 9:30 (30 minutes from 9:00)
solver.add(S + 30 <= 30)

# Brenda's busy blocks: 9:30-10:00 (30-60), 11:30-12:30 (150-180), 14:00-16:30 (300-450)
brenda_blocks = [(30, 60), (150, 180), (300, 450)]
for start, end in brenda_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Hannah has no constraints

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")