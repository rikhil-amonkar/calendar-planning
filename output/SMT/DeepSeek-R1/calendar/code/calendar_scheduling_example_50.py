from z3 import *

s = Int('s')
opt = Optimize()

# Convert work hours to minutes (9:00 = 0, 17:00 = 480)
opt.add(s >= 0)
opt.add(s + 60 <= 480)

# Emma's busy intervals (9:00-10:30, 11:00-12:00, 12:30-13:30, 14:30-15:30, 16:00-16:30)
emma_busy = [(0, 90), (120, 180), (210, 270), (330, 390), (420, 450)]
for start, end in emma_busy:
    opt.add(Or(s + 60 <= start, s >= end))

# Daniel and Roy have no constraints

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