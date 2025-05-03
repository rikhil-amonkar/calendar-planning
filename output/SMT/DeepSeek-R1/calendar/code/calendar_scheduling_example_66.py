from z3 import *

solver = Solver()
S = Int('S')

# Meeting must be within 9:00-17:00 (0 to 480 minutes) and last 1 hour
solver.add(S >= 0, S + 60 <= 480)

# Charles's busy intervals (converted to minutes since 9:00)
charles_busy = [
    (0, 90),     # 9:00-10:30
    (120, 150),  # 11:00-11:30
    (270, 300),  # 13:30-14:00
    (330, 360),  # 14:30-15:00
    (390, 450)   # 15:30-16:30
]

# Add constraints for Charles's availability
for start, end in charles_busy:
    solver.add(Or(S + 60 <= start, S >= end))

# Ronald and Maria have no constraints

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")