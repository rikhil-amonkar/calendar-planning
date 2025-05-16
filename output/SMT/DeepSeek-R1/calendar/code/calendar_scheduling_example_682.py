from z3 import *

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 30  # 30 minutes meeting

# Day must be Tuesday (Nathan cannot meet on Monday)
opt.add(day == 1)
opt.add(start >= 0)
opt.add(start + duration <= 480)  # 17:00 = 480 minutes from 9:00

# Blocked times in minutes since 9:00 (Tuesday only)
amanda_blocks = [(0, 30), (60, 90), (150, 180), (270, 330), (390, 420), (450, 480)]
nathan_blocks = [(0, 90), (120, 240), (270, 300), (330, 390), (420, 450)]

# Amanda's preference: meeting must end by 11:00 (120 minutes)
opt.add(start + duration <= 120)

# Add constraints avoiding blocked intervals
for s, e in amanda_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in nathan_blocks:
    opt.add(Or(start + duration <= s, start >= e))

# Find earliest possible time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    st = m[start].as_long()
    days = ['Monday', 'Tuesday']
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + duration) // 60
    end_m = (st + duration) % 60
    print(f"{days[1]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No valid slot found")