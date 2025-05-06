from z3 import Optimize, Int, Or, sat

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes

# Convert time constraints to minutes since 9:00 (0-480)
opt.add(start >= 0, start + duration <= 480)

# Nicole's busy periods (minutes since 9:00)
nicole_busy = [
    (0, 60),    # 9:00-10:00
    (90, 450)   # 10:30-16:30
]
for (s, e) in nicole_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Nicole's preference: start after 16:00 (420 minutes)
opt.add(start >= 420)

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