from z3 import *

s = Int('s')
opt = Optimize()

# Convert work hours to minutes (9:00 = 0, 17:00 = 480)
opt.add(s >= 0)
opt.add(s + 30 <= 480)

# Arthur's busy intervals (9:30-10:00, 14:00-14:30)
arthur_busy = [(30, 60), (300, 330)]
for start, end in arthur_busy:
    opt.add(Or(s + 30 <= start, s >= end))

# Theresa's busy intervals (9:00-9:30, 12:00-13:00, 15:00-16:30)
theresa_busy = [(0, 30), (180, 240), (360, 450)]
for start, end in theresa_busy:
    opt.add(Or(s + 30 <= start, s >= end))

# Carl's busy intervals (9:00-11:30, 12:00-14:00, 14:30-17:00)
carl_busy = [(0, 150), (180, 300), (330, 480)]
for start, end in carl_busy:
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