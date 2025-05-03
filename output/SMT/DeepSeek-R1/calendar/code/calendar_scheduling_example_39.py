from z3 import *

s = Int('s')
opt = Optimize()

# Convert work hours to minutes (9:00 = 0, 17:00 = 480)
opt.add(s >= 0)
opt.add(s + 30 <= 480)

# Victoria's busy intervals (13:30-14:00, 14:30-15:30, 16:30-17:00)
victoria_busy = [(270, 300), (330, 390), (450, 480)]
for start, end in victoria_busy:
    opt.add(Or(s + 30 <= start, s >= end))

# Nancy's busy intervals (9:00-14:00, 14:30-15:30)
nancy_busy = [(0, 300), (330, 390)]
for start, end in nancy_busy:
    opt.add(Or(s + 30 <= start, s >= end))

# Emily has no constraints

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