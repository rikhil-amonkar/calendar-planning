from z3 import Optimize, Int, sat

opt = Optimize()
start = Int('start')

# The meeting must be on Tuesday (Kyle is busy all Monday, Cheryl can't meet Wednesday)
# Time constraints in minutes since 9:00 (0-480, max start 450)
opt.add(start >= 0, start <= 450)

# Cheryl's Tuesday busy periods (minutes since 9:00)
cheryl_busy = [
    (360, 390)  # 15:00-15:30
]
for (s, e) in cheryl_busy:
    opt.add(Or(start + 30 <= s, start >= e))

# Kyle's Tuesday busy periods (minutes since 9:00)
kyle_busy = [
    (30, 480)  # 9:30-17:00
]
for (s, e) in kyle_busy:
    opt.add(Or(start + 30 <= s, start >= e))

# Find earliest possible time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    start_min = m[start].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts on Tuesday at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")