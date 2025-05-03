from z3 import *

s = Int('s')
opt = Optimize()

# Convert work hours to minutes (9:00 = 0, 17:00 = 480)
opt.add(s >= 0)
opt.add(s + 30 <= 480)

# Teresa's busy intervals (9:00-10:00, 13:00-13:30, 14:00-14:30, 15:00-15:30, 16:30-17:00)
teresa_busy = [(0, 60), (240, 270), (300, 330), (360, 390), (450, 480)]
for start, end in teresa_busy:
    opt.add(Or(s + 30 <= start, s >= end))

# Kathleen's busy intervals (9:00-9:30, 12:30-13:00, 13:30-14:00, 15:00-15:30) + preference (end by 14:30)
kathleen_busy = [(0, 30), (210, 240), (270, 300), (360, 390)]
for start, end in kathleen_busy:
    opt.add(Or(s + 30 <= start, s >= end))
opt.add(s + 30 <= 330)  # End by 14:30 (330 minutes)

# Patricia's busy intervals (9:00-10:30, 11:30-12:00, 13:00-13:30, 14:00-14:30, 15:30-16:00, 16:30-17:00)
patricia_busy = [(0, 90), (150, 180), (240, 270), (300, 330), (390, 420), (450, 480)]
for start, end in patricia_busy:
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