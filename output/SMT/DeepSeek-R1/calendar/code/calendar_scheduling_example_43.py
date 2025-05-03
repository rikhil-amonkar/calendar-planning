from z3 import *

s = Int('s')
opt = Optimize()

# Convert work hours to minutes (9:00 = 0, 17:00 = 480)
opt.add(s >= 0)
opt.add(s + 30 <= 480)

# Albert's busy intervals (9:30-10:30, 12:00-12:30, 14:00-14:30, 15:00-15:30, 16:30-17:00)
albert_busy = [(30, 90), (180, 210), (300, 330), (360, 390), (450, 480)]
for start, end in albert_busy:
    opt.add(Or(s + 30 <= start, s >= end))

# Gregory's busy intervals (11:00-11:30, 12:30-13:00, 13:30-14:00, 15:30-16:00)
gregory_busy = [(120, 150), (210, 240), (270, 300), (390, 420)]
for start, end in gregory_busy:
    opt.add(Or(s + 30 <= start, s >= end))

# Benjamin's busy intervals (9:30-10:00, 10:30-11:00, 11:30-13:30, 14:00-15:00, 15:30-16:00, 16:30-17:00)
benjamin_busy = [(30, 60), (90, 120), (150, 270), (300, 360), (390, 420), (450, 480)]
for start, end in benjamin_busy:
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