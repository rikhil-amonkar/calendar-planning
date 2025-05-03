from z3 import *

s = Int('s')
opt = Optimize()

# Convert work hours to minutes (9:00 = 0, 17:00 = 480)
opt.add(s >= 0)
opt.add(s + 60 <= 480)

# Alice's busy intervals (9:30-10:00, 12:30-13:00, 14:30-15:00, 16:30-17:00)
alice_busy = [(30, 60), (210, 240), (330, 360), (450, 480)]
for start, end in alice_busy:
    opt.add(Or(s + 60 <= start, s >= end))

# Arthur's busy intervals (9:00-9:30, 10:00-11:00, 11:30-12:00, 13:00-14:00, 15:00-15:30, 16:30-17:00)
arthur_busy = [(0, 30), (60, 120), (150, 180), (240, 300), (360, 390), (450, 480)]
for start, end in arthur_busy:
    opt.add(Or(s + 60 <= start, s >= end))

# Noah has no constraints

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