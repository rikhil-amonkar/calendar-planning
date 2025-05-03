from z3 import *

opt = Optimize()
S = Int('S')

# Convert all times to minutes since 9:00
# Meeting must be 30 minutes and fit within 9:00-17:00 (0-480 minutes)
opt.add(S >= 0, S + 30 <= 480)

# Lauren's constraints
lauren_busy = [
    (0, 90),    # 9:00-10:30 (0-90)
    (330, 480)  # 14:30-17:00 (330-480)
]
for start, end in lauren_busy:
    opt.add(Or(S + 30 <= start, S >= end))

# Michael's constraints
michael_busy = [
    (60, 90),    # 10:00-10:30
    (150, 180),  # 11:30-12:00
    (270, 300),  # 13:30-14:00
    (390, 420)   # 15:30-16:00
]
for start, end in michael_busy:
    opt.add(Or(S + 30 <= start, S >= end))

# Bryan has no constraints

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