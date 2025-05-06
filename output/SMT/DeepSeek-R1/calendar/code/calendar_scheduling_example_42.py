from z3 import Optimize, Int, Or, sat

opt = Optimize()
start = Int('start')
duration = 60  # 1 hour

# Convert time constraints to minutes since 9:00 (0-480)
opt.add(start >= 0, start + duration <= 480)

# Julie's busy periods (minutes since 9:00)
julie_busy = [
    (0, 30),    # 9:00-9:30
    (120, 150), # 11:00-11:30
    (180, 210), # 12:00-12:30
    (270, 300), # 13:30-14:00
    (420, 480)  # 16:00-17:00
]
for (s, e) in julie_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Sean's busy periods
sean_busy = [
    (0, 30),    # 9:00-9:30
    (240, 270), # 13:00-13:30
    (360, 390), # 15:00-15:30
    (420, 450)  # 16:00-16:30
]
for (s, e) in sean_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Lori's busy periods
lori_busy = [
    (60, 90),   # 10:00-10:30
    (120, 240), # 11:00-13:00
    (390, 480)  # 15:30-17:00
]
for (s, e) in lori_busy:
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