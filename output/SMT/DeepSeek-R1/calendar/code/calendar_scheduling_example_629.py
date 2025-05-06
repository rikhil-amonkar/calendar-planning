from z3 import Optimize, Int, If, Or, And, sat

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 30  # 30 minutes

# Days: Monday(0), Tuesday(1)
opt.add(day >= 0, day <= 1)
opt.add(start >= 0, start + duration <= 480)

# Margaret cannot meet on Monday and wants Tuesday after 14:30 (330 minutes)
opt.add(day == 1)  # Only Tuesday allowed
opt.add(start >= 330)  # 14:30 in minutes

# Margaret's Tuesday busy periods (converted to minutes)
margaret_busy = [
    (180, 210)  # 12:00-12:30
]
for (s, e) in margaret_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Alexis's Tuesday busy periods (converted to minutes)
alexis_busy = [
    (0, 30),    # 9:00-9:30
    (60, 90),    # 10:00-10:30
    (300, 450)   # 14:00-16:30
]
for (s, e) in alexis_busy:
    opt.add(Or(start + duration <= s, start >= e))

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