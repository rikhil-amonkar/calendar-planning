from z3 import *

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 60  # 1 hour meeting

# Day must be between Monday (0) and Thursday (3)
opt.add(day >= 0, day <= 3)
opt.add(start >= 0)
opt.add(start + duration <= 480)  # 17:00 = 480 minutes

# Natalie's blocked times per day (in minutes since 9:00)
natalie_blocks = [
    [(0, 30), (60, 180), (150, 180), (300, 330), (360, 450)],  # Monday
    [(0, 30), (60, 90), (150, 240), (420, 480)],               # Tuesday
    [(120, 150), (420, 450)],                                   # Wednesday
    [(60, 120), (150, 360), (390, 420), (450, 480)]             # Thursday
]

# William's blocked times per day (in minutes since 9:00)
william_blocks = [
    [(30, 120), (150, 480)],    # Monday
    [(0, 240), (270, 420)],     # Tuesday
    [(0, 210), (240, 330), (390, 420), (450, 480)],  # Wednesday
    [(0, 90), (120, 150), (180, 210), (240, 300), (360, 480)]  # Thursday
]

# Add constraints for each day's blocked intervals
for d in range(4):
    # Natalie's constraints for day d
    for s, e in natalie_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= s, start >= e)))
    # William's constraints for day d
    for s, e in william_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= s, start >= e)))

# Optimize for earliest day and earliest time
opt.minimize(day * 1000 + start)  # Prioritize day first, then start time

if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    st = m[start].as_long()
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + duration) // 60
    end_m = (st + duration) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No valid slot found")