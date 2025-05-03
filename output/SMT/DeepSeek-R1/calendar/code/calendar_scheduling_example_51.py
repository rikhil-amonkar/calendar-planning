from z3 import *

s = Int('s')
opt = Optimize()

# Convert work hours to minutes (9:00 = 0, 17:00 = 480)
opt.add(s >= 0)
opt.add(s + 60 <= 480)

# Brandon's busy intervals (11:30-12:00, 12:30-13:30, 14:00-14:30)
brandon_busy = [(150, 180), (210, 270), (300, 330)]
for start, end in brandon_busy:
    opt.add(Or(s + 60 <= start, s >= end))

# Donna's busy intervals (10:00-10:30, 12:00-12:30)
donna_busy = [(60, 90), (180, 210)]
for start, end in donna_busy:
    opt.add(Or(s + 60 <= start, s >= end))

# Jack's busy intervals (9:30-10:00, 10:30-11:00, 11:30-12:30, 13:00-14:30, 15:30-17:00)
jack_busy = [(30, 60), (90, 120), (150, 210), (240, 330), (390, 480)]
for start, end in jack_busy:
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