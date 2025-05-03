from z3 import *

solver = Solver()
S = Int('S')

# Convert all times to minutes since 9:00 (0-480)
# Meeting must be 1 hour (60 minutes) within 9:00-17:00
solver.add(S >= 0, S + 60 <= 480)

# Shirley's busy periods (120-150, 300-360, 420-450)
shirley_busy = [
    (120, 150),  # 11:00-11:30
    (300, 360),  # 14:00-15:00
    (420, 450)   # 16:00-16:30
]
for start, end in shirley_busy:
    solver.add(Or(S + 60 <= start, S >= end))

# Stephen's busy periods (240-270, 390-420)
stephen_busy = [
    (240, 270),  # 13:00-13:30
    (390, 420)   # 15:30-16:00
]
for start, end in stephen_busy:
    solver.add(Or(S + 60 <= start, S >= end))

# Paul's busy periods (0-60, 120-480)
paul_busy = [
    (0, 60),     # 9:00-10:00
    (120, 480)   # 11:00-17:00
]
for start, end in paul_busy:
    solver.add(Or(S + 60 <= start, S >= end))

# Find the earliest possible time (use Optimize instead of Solver for minimization)
opt = Optimize()
opt.add(solver.assertions())
opt.minimize(S)

if opt.check() == sat:
    m = opt.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")