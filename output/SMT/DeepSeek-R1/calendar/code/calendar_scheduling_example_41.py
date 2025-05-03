from z3 import *

s = Int('s')
opt = Optimize()

# Convert work hours to minutes (9:00 = 0, 17:00 = 480)
opt.add(s >= 330)  # Alan's preference (14:30)
opt.add(s + 30 <= 480)

# Nancy's busy intervals (11:00-12:30, 13:00-13:30, 14:00-15:00)
nancy_busy = [(120, 210), (240, 270), (300, 360)]
for start, end in nancy_busy:
    opt.add(Or(s + 30 <= start, s >= end))

# Patricia's busy intervals (10:00-12:00, 12:30-13:00, 13:30-16:00)
patricia_busy = [(60, 180), (210, 240), (270, 420)]
for start, end in patricia_busy:
    opt.add(Or(s + 30 <= start, s >= end))

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