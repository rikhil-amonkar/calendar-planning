from z3 import *

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 60  # 1 hour meeting

# Day must be between Monday (0) and Friday (4)
opt.add(day >= 0, day <= 4)
opt.add(start >= 0)
opt.add(start + duration <= 480)  # 17:00 = 480 minutes

# Brian's blocked times per day (minutes since 9:00)
brian_blocks = [
    [(30, 60), (210, 330), (390, 420)],  # Monday
    [(0, 30)],                             # Tuesday
    [(210, 300), (450, 480)],              # Wednesday
    [(120, 150), (240, 270), (450, 480)],  # Thursday
    [(30, 60), (90, 120), (240, 270), (360, 420), (450, 480)]  # Friday
]

# Julia's blocked times per day (minutes since 9:00)
julia_blocks = [
    [(0, 60), (120, 150), (210, 240), (390, 420)],  # Monday
    [(240, 300), (420, 450)],                        # Tuesday
    [(0, 150), (180, 210), (240, 480)],              # Wednesday
    [(0, 90), (120, 480)],                           # Thursday
    [(0, 60), (90, 150), (210, 300), (330, 360), (390, 420)]  # Friday
]

# Add constraints for each day's blocked intervals
for d in range(5):
    # Brian's constraints for day d
    for s, e in brian_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= s, start >= e)))
    # Julia's constraints for day d
    for s, e in julia_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= s, start >= e)))

# Cost function: penalize Monday (day 0) with 1000, then day*480 + start
cost = day * 480 + start + If(day == 0, 1000, 0)
opt.minimize(cost)

if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    st = m[start].as_long()
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + duration) // 60
    end_m = (st + duration) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No valid slot found")