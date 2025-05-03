from z3 import *

s = Int('s')
opt = Optimize()

# Convert work hours to minutes (9:00 = 0, 17:00 = 480)
opt.add(s >= 0)
opt.add(s + 60 <= 480)

# Isabella's busy intervals (11:00-11:30, 15:30-16:00)
isabella_busy = [(120, 150), (390, 420)]
for start, end in isabella_busy:
    opt.add(Or(s + 60 <= start, s >= end))

# Tyler's busy intervals (9:00-10:00) + end by 16:00 constraint
tyler_busy = [(0, 60)]
for start, end in tyler_busy:
    opt.add(Or(s + 60 <= start, s >= end))
opt.add(s + 60 <= 420)  # Must end by 16:00

# Jordan's busy intervals (9:00-10:00, 10:30-11:00, 12:30-13:30, 14:00-14:30, 15:00-16:00)
jordan_busy = [(0, 60), (90, 120), (210, 270), (300, 330), (360, 420)]
for start, end in jordan_busy:
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