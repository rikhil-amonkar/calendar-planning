from z3 import *

s = Int('s')
opt = Optimize()

# Convert work hours to minutes (9:00 = 0, 17:00 = 480)
opt.add(s >= 0)
opt.add(s + 60 <= 480)

# Eric's busy intervals (9:00-9:30, 10:30-11:30, 15:00-15:30)
eric_busy = [(0, 30), (90, 150), (360, 390)]
for start, end in eric_busy:
    opt.add(Or(s + 60 <= start, s >= end))

# Roger's busy intervals (9:30-10:30, 11:00-12:00, 12:30-13:00, 14:30-15:00, 15:30-16:30)
roger_busy = [(30, 90), (120, 180), (210, 240), (330, 360), (390, 450)]
for start, end in roger_busy:
    opt.add(Or(s + 60 <= start, s >= end))

# David has no constraints

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