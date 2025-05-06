from z3 import Optimize, Int, Or, sat

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes

# Convert time constraints to minutes since 9:00 (0-480)
opt.add(start >= 0, start + duration <= 480)

# Megan's preference: start after 10:00 (60 minutes)
opt.add(start >= 60)

# Kimberly's busy periods
kimberly_busy = [
    (60, 90),    # 10:00-10:30
    (120, 180),  # 11:00-12:00
    (420, 450)   # 16:00-16:30
]
for (s, e) in kimberly_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Marie's busy periods
marie_busy = [
    (60, 120),   # 10:00-11:00
    (150, 360),  # 11:30-15:00
    (420, 450)   # 16:00-16:30
]
for (s, e) in marie_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Diana's busy periods
diana_busy = [
    (30, 60),    # 9:30-10:00
    (90, 330),   # 10:30-14:30
    (390, 480)   # 15:30-17:00
]
for (s, e) in diana_busy:
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