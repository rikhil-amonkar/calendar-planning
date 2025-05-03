from z3 import *

opt = Optimize()
S = Int('S')

# Convert all times to minutes since 9:00 (0-480)
# Meeting must be 30 minutes and fit within 9:00-17:00
opt.add(S >= 0, S + 30 <= 480)

# Denise's constraints (busy at 180-210, 390-420)
denise_busy = [
    (180, 210),  # 12:00-12:30
    (390, 420)   # 15:30-16:00
]
for start, end in denise_busy:
    opt.add(Or(S + 30 <= start, S >= end))

# Natalie's constraints (busy at 0-150, 180-240, 300-330, 360-480)
natalie_busy = [
    (0, 150),    # 9:00-11:30
    (180, 240),  # 12:00-13:00
    (300, 330),  # 14:00-14:30
    (360, 480)   # 15:00-17:00
]
for start, end in natalie_busy:
    opt.add(Or(S + 30 <= start, S >= end))

# Angela has no constraints

# Find earliest possible time
opt.minimize(S)

if opt.check() == sat:
    m = opt.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")