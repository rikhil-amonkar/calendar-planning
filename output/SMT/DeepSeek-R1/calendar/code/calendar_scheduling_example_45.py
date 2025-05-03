from z3 import *

s = Int('s')
opt = Optimize()

# Convert work hours to minutes (9:00 = 0, 17:00 = 480)
opt.add(s >= 0)
opt.add(s + 30 <= 480)

# Samuel's busy intervals (9:00-10:30, 11:30-12:00, 13:00-13:30, 14:00-16:00, 16:30-17:00)
samuel_busy = [(0, 90), (150, 180), (240, 270), (300, 420), (450, 480)]
for start, end in samuel_busy:
    opt.add(Or(s + 30 <= start, s >= end))

# Andrew and Grace have no constraints

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