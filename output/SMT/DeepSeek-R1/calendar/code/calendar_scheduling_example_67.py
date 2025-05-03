from z3 import *

solver = Solver()
S = Int('S')

# Convert all times to minutes since 9:00
# Meeting must be 30 minutes and end by 14:00 (300 minutes) due to Linda's constraint
solver.add(S >= 0, S + 30 <= 300)  # 300 minutes = 14:00 (9:00 + 5h)

# Jacqueline's busy intervals (13:00-13:30 = 240-270 minutes)
solver.add(Or(S + 30 <= 240, S >= 270))

# Linda's constraints: busy periods and can't meet after 14:00
# Busy periods: 9:00-10:30 (0-90), 11:30-12:30 (150-180)
solver.add(S >= 90)  # Must start after 10:30
solver.add(Or(S + 30 <= 150, S >= 180))  # Avoid 11:30-12:30 (150-180)

# Christian has no constraints

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")