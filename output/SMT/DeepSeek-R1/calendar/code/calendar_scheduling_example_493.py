from z3 import Optimize, Int, Or, sat

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes

# Convert time constraints to minutes since 9:00 (0-480)
opt.add(start >= 0, start + duration <= 480)

# Stephanie's busy periods (minutes since 9:00)
stephanie_busy = [
    (120, 150),  # 11:00-11:30
    (330, 360)   # 14:30-15:00
]
for (s, e) in stephanie_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Joe's busy periods
joe_busy = [
    (0, 30),     # 9:00-9:30
    (60, 180),   # 10:00-12:00
    (210, 240),  # 12:30-13:00
    (300, 480)   # 14:00-17:00
]
for (s, e) in joe_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Diana's busy periods
diana_busy = [
    (0, 90),     # 9:00-10:30
    (150, 180),  # 11:30-12:00
    (240, 300),  # 13:00-14:00
    (330, 390),  # 14:30-15:30
    (420, 480)   # 16:00-17:00
]
for (s, e) in diana_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Deborah's busy periods
deborah_busy = [
    (0, 60),     # 9:00-10:00
    (90, 180),   # 10:30-12:00
    (210, 240),  # 12:30-13:00
    (270, 300),  # 13:30-14:00
    (330, 390),  # 14:30-15:30
    (420, 450)   # 16:00-16:30
]
for (s, e) in deborah_busy:
    opt.add(Or(start + duration <= s, start >= e))

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