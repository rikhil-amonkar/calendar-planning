from z3 import *

opt = Optimize()

day = Int('day')
start = Int('start')
duration = 30  # Meeting duration in minutes

# Day constraints: 0=Monday, 1=Tuesday, 2=Wednesday
opt.add(day >= 0, day <= 2)
opt.add(start >= 0)
opt.add(start + duration <= 480)  # 17:00 = 480 minutes from 9:00

# Blocked time ranges in minutes from 9:00 (day, person: 0=Ronald, 1=Amber)
ronald_blocks = {
    0: [(90, 120), (180, 210), (390, 420)],
    1: [(0, 30), (180, 210), (390, 450)],
    2: [(30, 90), (120, 180), (210, 240), (270, 300), (450, 480)]
}

amber_blocks = {
    0: [(0, 30), (60, 90), (150, 180), (210, 300), (330, 360), (390, 480)],
    1: [(0, 30), (60, 150), (180, 210), (270, 390), (450, 480)],
    2: [(0, 30), (60, 90), (120, 270), (360, 390)]
}

# Add constraints for each day's availability
for d in [0, 1, 2]:
    # Ronald's availability
    for (s, e) in ronald_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= s, start >= e)))
    # Amber's availability
    for (s, e) in amber_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= s, start >= e)))

# Optimize for earliest possible time (minimize day*1000 + start)
opt.minimize(day * 1000 + start)

if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    st = m[start].as_long()
    days = ['Monday', 'Tuesday', 'Wednesday']
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + duration) // 60
    end_m = (st + duration) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No valid slot found")