from z3 import Optimize, Int, Or, sat

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes

# Convert time constraints to minutes since 9:00 (0-480)
opt.add(start >= 0, start + duration <= 480)

# Wayne's preference: start after 14:00 (300 minutes)
opt.add(start >= 300)

# Melissa's busy periods
melissa_busy = [
    (60, 120),   # 10:00-11:00
    (210, 300),  # 12:30-14:00
    (360, 390)   # 15:00-15:30
]
for (s, e) in melissa_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Gregory's busy periods
gregory_busy = [
    (210, 240),  # 12:30-13:00
    (450, 480)   # 15:30-16:00
]
for (s, e) in gregory_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Victoria's busy periods
victoria_busy = [
    (0, 30),     # 9:00-9:30
    (90, 150),   # 10:30-11:30
    (240, 300),  # 13:00-14:00
    (330, 360),  # 14:30-15:00
    (450, 510)   # 15:30-16:30 (adjusted to 480 max)
]
for (s, e) in victoria_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Thomas's busy periods
thomas_busy = [
    (60, 180),   # 10:00-12:00
    (210, 240),  # 12:30-13:00
    (330, 420)   # 14:30-16:00
]
for (s, e) in thomas_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Jennifer's busy periods
jennifer_busy = [
    (0, 30),     # 9:00-9:30
    (60, 90),    # 10:00-10:30
    (120, 240),  # 11:00-13:00
    (270, 330),  # 13:30-14:30
    (360, 390),  # 15:00-15:30
    (420, 450)   # 16:00-16:30
]
for (s, e) in jennifer_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Catherine and Roger have no constraints

# Find earliest possible time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    start_min = m[start].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts on Monday at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")