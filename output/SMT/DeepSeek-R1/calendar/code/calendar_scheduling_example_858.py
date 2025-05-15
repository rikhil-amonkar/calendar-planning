from z3 import *

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 60  # 1 hour meeting

# Day constraints: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
opt.add(day >= 0, day <= 3)
# Start time constraints (minutes since 9:00)
opt.add(start >= 0, start + duration <= 480)

# Carl's blocked times (converted to minutes since 9:00 per day)
carl_blocks = {
    0: [(120, 150)],          # Monday 11:00-11:30
    1: [(330, 360)],          # Tuesday 14:30-15:00
    2: [(60, 150), (240, 270)], # Wednesday 10:00-11:30, 13:00-13:30
    3: [(270, 300), (420, 450)] # Thursday 13:30-14:00, 16:00-16:30
}

# Margaret's blocked times (same conversion)
margaret_blocks = {
    0: [(0, 90), (120, 480)],    # Monday 9:00-10:30, 11:00-17:00
    1: [(30, 180), (270, 300), (390, 480)],  # Tuesday 9:30-12:00, 13:30-14:00, 15:30-17:00
    2: [(30, 180), (210, 240), (270, 330), (360, 480)], # Wednesday 9:30-12:00, 12:30-13:00, 13:30-14:30, 15:00-17:00
    3: [(60, 180), (210, 300), (330, 480)]  # Thursday 10:00-12:00, 12:30-14:00, 14:30-17:00
}

# Add constraints for each day's availability
for d in range(4):
    # Carl's availability for day d
    for block_start, block_end in carl_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= block_start, start >= block_end)))
    # Margaret's availability for day d
    for block_start, block_end in margaret_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= block_start, start >= block_end)))

# Prefer earlier days (Carl wants to avoid Thursday) and earlier times
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    st = m[start].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_str = days[d]
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + duration) // 60
    end_m = (st + duration) % 60
    print(f"{day_str} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No valid slot found")