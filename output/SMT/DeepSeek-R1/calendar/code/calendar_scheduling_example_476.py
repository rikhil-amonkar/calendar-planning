from z3 import Optimize, Int, Or, sat

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes

# Convert time constraints to minutes since 9:00 (0-450)
opt.add(start >= 0, start + duration <= 480)

# Roger's preference: start after 12:30 (210 minutes)
opt.add(start >= 210)

# Kathleen's busy periods
kathleen_busy = [(330, 390)]
for (s, e) in kathleen_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Carolyn's busy periods
carolyn_busy = [(180, 210), (240, 270)]
for (s, e) in carolyn_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Cheryl's busy periods
cheryl_busy = [(0, 30), (60, 150), (210, 270), (300, 480)]
for (s, e) in cheryl_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Virginia's busy periods
virginia_busy = [(30, 150), (180, 210), (240, 270), (330, 390), (420, 480)]
for (s, e) in virginia_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Angela's busy periods
angela_busy = [(30, 60), (90, 150), (180, 210), (240, 270), (300, 450)]
for (s, e) in angela_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Daniel and Roger have no other constraints beyond Roger's time preference

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