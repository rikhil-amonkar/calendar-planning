from z3 import *

s = Int('s')
opt = Optimize()

# Convert work hours to minutes (9:00 = 0, 17:00 = 480)
opt.add(s >= 0)
opt.add(s + 60 <= 480)

# Julie's busy intervals (9:00-9:30, 11:00-11:30, 12:00-12:30, 13:30-14:00, 16:00-17:00)
julie_busy = [(0, 30), (120, 150), (180, 210), (270, 300), (420, 480)]
for start, end in julie_busy:
    opt.add(Or(s + 60 <= start, s >= end))

# Sean's busy intervals (9:00-9:30, 13:00-13:30, 15:00-15:30, 16:00-16:30)
sean_busy = [(0, 30), (240, 270), (360, 390), (420, 450)]
for start, end in sean_busy:
    opt.add(Or(s + 60 <= start, s >= end))

# Lori's busy intervals (10:00-10:30, 11:00-13:00, 15:30-17:00)
lori_busy = [(60, 90), (120, 240), (390, 480)]
for start, end in lori_busy:
    opt.add(Or(s + 60 <= start, s >= end))

# Find earliest possible time
opt.minimize(s)

if opt.check() == sat:
    m = opt.model()
    start_min = m[s].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No solution found")