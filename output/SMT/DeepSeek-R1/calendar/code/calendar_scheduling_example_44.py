from z3 import *

s = Int('s')
opt = Optimize()

# Convert work hours to minutes (9:00 = 0, 17:00 = 480)
opt.add(s >= 0)
opt.add(s + 30 <= 240)  # Isabella's preference (end by 13:00)

# Ronald's busy intervals (11:30-12:00, 14:00-14:30, 16:00-17:00)
ronald_busy = [(150, 180), (300, 330), (420, 480)]
for start, end in ronald_busy:
    opt.add(Or(s + 30 <= start, s >= end))

# Amanda's busy intervals (9:30-12:00, 12:30-13:00, 13:30-14:00, 15:30-17:00)
amanda_busy = [(30, 180), (210, 240), (270, 300), (390, 480)]
for start, end in amanda_busy:
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