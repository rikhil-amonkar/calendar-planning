from z3 import Optimize, Int, Or, sat

opt = Optimize()
start = Int('start')

# The meeting must be on Wednesday (Jose is busy Mon/Tue)
# Time constraints in minutes since 9:00 (0-480, max start 450)
opt.add(start >= 0, start <= 450)

# Nancy's Wednesday busy periods (minutes since 9:00)
nancy_busy = [
    (60, 150),    # 10:00-11:30
    (270, 420)    # 13:30-16:00
]
for (s, e) in nancy_busy:
    opt.add(Or(start + 30 <= s, start >= e))

# Jose's Wednesday busy periods
jose_busy = [
    (0, 30),      # 9:00-9:30
    (60, 210),    # 10:00-12:30
    (270, 330),   # 13:30-14:30
    (360, 480)    # 15:00-17:00
]
for (s, e) in jose_busy:
    opt.add(Or(start + 30 <= s, start >= e))

# Find the earliest possible time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    start_min = m[start].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts on Wednesday at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")