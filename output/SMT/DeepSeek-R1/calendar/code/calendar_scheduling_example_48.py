from z3 import *

s = Int('s')
opt = Optimize()

# Convert work hours to minutes (9:00 = 0, 17:00 = 480)
opt.add(s >= 270)  # Cynthia's preference (not before 13:30)
opt.add(s + 60 <= 480)

# Janet's busy intervals (9:30-10:30, 12:30-13:00, 14:00-14:30)
janet_busy = [(30, 90), (210, 240), (300, 330)]
for start, end in janet_busy:
    opt.add(Or(s + 60 <= start, s >= end))

# Cynthia's busy intervals (9:30-10:00, 11:00-11:30, 12:30-14:30, 16:00-17:00)
cynthia_busy = [(30, 60), (120, 150), (210, 330), (420, 480)]
for start, end in cynthia_busy:
    opt.add(Or(s + 60 <= start, s >= end))

# Rachel has no constraints

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