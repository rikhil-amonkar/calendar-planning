from z3 import *

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 60  # 1 hour meeting

# Day constraints: 2=Wednesday, 4=Friday (Monday, Tuesday, Thursday excluded)
opt.add(Or(day == 2, day == 4))
opt.add(start >= 0)
opt.add(start + duration <= 480)  # 17:00 = 480 minutes from 9:00

# Blocked times in minutes since 9:00 (day, start, end)
bryan_blocks = {
    4: [(90, 120), (300, 330)]  # Friday blocked times
}

nicholas_blocks = {
    2: [(0, 30), (60, 120), (150, 270), (300, 330), (360, 450)],  # Wednesday
    4: [(0, 90), (120, 180), (210, 330), (390, 420), (450, 480)]   # Friday
}

# Add constraints for allowed days
for d in [2, 4]:
    # Bryan's constraints (only Friday has blocks)
    for b_start, b_end in bryan_blocks.get(d, []):
        opt.add(Implies(day == d, Or(start + duration <= b_start, start >= b_end)))
    # Nicholas's constraints
    for b_start, b_end in nicholas_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= b_start, start >= b_end)))

# Optimize for earliest possible time (day*1000 + start)
opt.minimize(day * 1000 + start)

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