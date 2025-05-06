from z3 import *

s = Optimize()

day = Int('day')
start_time = Int('start_time')

# Day constraints (0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday)
s.add(day >= 0)
s.add(day <= 3)

# Basic time constraints (minutes since 9:00)
s.add(start_time >= 0)
s.add(start_time + 60 <= 480)  # 1-hour duration

# Megan's busy blocks (converted to minutes since 9:00)
megan_busy = {
    0: [(240, 270), (300, 390)],   # Monday
    1: [(0, 30), (180, 210), (420, 480)],  # Tuesday
    2: [(30, 60), (90, 150), (210, 300), (420, 450)],  # Wednesday
    3: [(270, 330), (360, 390)]   # Thursday
}

# Daniel's busy blocks
daniel_busy = {
    0: [(60, 150), (210, 360)],   # Monday
    1: [(0, 60), (90, 480)],      # Tuesday
    2: [(0, 60), (90, 150), (180, 480)],  # Wednesday
    3: [(0, 180), (210, 330), (360, 390), (420, 480)]  # Thursday
}

# Add constraints for Megan's availability
for d, blocks in megan_busy.items():
    for block_start, block_end in blocks:
        s.add(Implies(day == d, Or(
            start_time + 60 <= block_start,
            start_time >= block_end
        )))

# Add constraints for Daniel's availability
for d, blocks in daniel_busy.items():
    for block_start, block_end in blocks:
        s.add(Implies(day == d, Or(
            start_time + 60 <= block_start,
            start_time >= block_end
        )))

# Optimize for earliest possible time (day first, then start time)
s.minimize(day * 1000 + start_time)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start_time].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 60) // 60
    end_m = (st + 60) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")