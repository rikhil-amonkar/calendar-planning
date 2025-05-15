from z3 import *

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 30  # 30 minutes meeting

# Day constraints: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
opt.add(day >= 0, day <= 4)
# Start time constraints (minutes since 9:00)
opt.add(start >= 0, start + duration <= 480)

# Frances prefers to avoid Tuesday (day 1)
opt.add(day != 1)

# Convert blocked times to minutes since 9:00 per day
terry_blocks = {
    0: [(90, 120), (210, 300), (360, 480)],   # Monday
    1: [(30, 60), (90, 120), (300, 330), (420, 450)],  # Tuesday
    2: [(30, 90), (60, 120), (180, 210), (330, 420), (450, 480)],  # Wednesday
    3: [(30, 60), (180, 210), (240, 330), (420, 450)],  # Thursday
    4: [(0, 150), (180, 210), (270, 420), (450, 480)]   # Friday
}

frances_blocks = {
    0: [(30, 120), (150, 240), (300, 330), (360, 420)],  # Monday
    1: [(0, 30), (60, 90), (120, 180), (240, 330), (390, 420)],  # Tuesday
    2: [(30, 60), (90, 120), (150, 420), (450, 480)],    # Wednesday
    3: [(120, 210), (270, 480)],                         # Thursday
    4: [(30, 90), (120, 210), (240, 420), (450, 480)]    # Friday
}

# Add constraints for each day's availability
for d in range(5):
    # Terry's availability
    for block_start, block_end in terry_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= block_start, start >= block_end)))
    # Frances's availability
    for block_start, block_end in frances_blocks[d]:
        opt.add(Implies(day == d, Or(start + duration <= block_start, start >= block_end)))

# Optimize for earliest possible day and time
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    st = m[start].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_str = days[d]
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + duration) // 60
    end_m = (st + duration) % 60
    print(f"{day_str} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No valid slot found")