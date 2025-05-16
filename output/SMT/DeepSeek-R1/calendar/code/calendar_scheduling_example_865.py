from z3 import *

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 60  # 1 hour meeting

# Day constraints: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
opt.add(day >= 0, day <= 3)
opt.add(start >= 0)
opt.add(start + duration <= 480)  # 17:00 = 480 minutes from 9:00

# Blocked times in minutes since 9:00 (day, start, end)
megan_blocks = {
    0: [(240, 270), (300, 390)],    # Monday
    1: [(0, 30), (180, 210), (420, 480)],  # Tuesday
    2: [(30, 60), (90, 150), (210, 300), (420, 450)],  # Wednesday
    3: [(270, 330), (360, 390)]     # Thursday
}

daniel_blocks = {
    0: [(60, 150), (210, 360)],     # Monday
    1: [(0, 60), (90, 480)],        # Tuesday
    2: [(0, 60), (90, 150), (180, 480)],  # Wednesday
    3: [(0, 180), (210, 330), (360, 390), (420, 480)]  # Thursday
}

# Add constraints for each day
for d in [0, 1, 2, 3]:
    # Megan's availability
    for (s, e) in megan_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= s, start >= e)))
    # Daniel's availability
    for (s, e) in daniel_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= s, start >= e)))

# Optimize for earliest possible time (minimize day*1000 + start)
opt.minimize(day * 1000 + start)

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