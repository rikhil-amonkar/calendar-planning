from z3 import *

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 30  # 30 minutes meeting

# Day constraints: 0=Monday, 1=Tuesday, 2=Wednesday
opt.add(day >= 0, day <= 2)
# Start time constraints (minutes since 9:00)
opt.add(start >= 0, start + duration <= 480)

# Nicole's blocked times (minutes since 9:00 per day)
nicole_blocks = {
    0: [(0, 30), (240, 270), (330, 390)],     # Monday blocks
    1: [(0, 30), (150, 270), (330, 390)],     # Tuesday blocks
    2: [(60, 120), (210, 360), (420, 480)]    # Wednesday blocks
}

# Ruth's blocked times (minutes since 9:00 per day)
ruth_blocks = {
    0: [(0, 480)],                            # Monday full day
    1: [(0, 480)],                            # Tuesday full day
    2: [(0, 90), (120, 150), (180, 210), (270, 390), (420, 450)]  # Wednesday blocks
}

# Add constraints for each day's availability
for d in range(3):
    # Nicole's availability
    for block_start, block_end in nicole_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= block_start, start >= block_end)))
    # Ruth's availability
    for block_start, block_end in ruth_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= block_start, start >= block_end)))

# Ruth's Wednesday constraint: meeting must end by 13:30 (270 minutes)
opt.add(Implies(day == 2, start + duration <= 270))

# Optimize for earliest possible day and time
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    st = m[start].as_long()
    days = ["Monday", "Tuesday", "Wednesday"]
    day_str = days[d]
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + duration) // 60
    end_m = (st + duration) % 60
    print(f"{day_str} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No valid slot found")