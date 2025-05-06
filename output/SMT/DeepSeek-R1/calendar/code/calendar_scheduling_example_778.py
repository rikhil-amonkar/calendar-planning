from z3 import *

s = Optimize()

day = Int('day')
start_time = Int('start_time')

# Day constraints (0=Monday, 1=Tuesday, 2=Wednesday)
s.add(day >= 0)
s.add(day <= 2)

# Basic time constraints (minutes since 9:00)
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)

# Susan's preferences: avoid Tuesday if possible (soft constraint)
preference = If(day == 1, 1, 0)
s.add(preference == 0)

# Sandra can't meet on Monday after 16:00 (420 minutes)
s.add(Implies(day == 0, start_time + 30 <= 420))

# Susan's busy blocks (converted to minutes since 9:00)
susan_busy = {
    0: [(210, 240), (270, 300)],   # Monday: 12:30-13:00, 13:30-14:00
    1: [(150, 180)],               # Tuesday: 11:30-12:00
    2: [(30, 90), (300, 330), (390, 450)]  # Wednesday: 9:30-10:30, 14:00-14:30, 15:30-16:30
}

# Sandra's busy blocks
sandra_busy = {
    0: [(0, 240), (300, 360), (420, 450)],  # Monday: 9:00-13:00, 14:00-15:00, 16:00-16:30
    1: [(0, 30), (90, 180), (210, 270), (300, 330), (420, 480)],  # Tuesday
    2: [(0, 150), (180, 210), (240, 480)]  # Wednesday
}

# Add constraints for Susan's availability
for d, blocks in susan_busy.items():
    for block_start, block_end in blocks:
        s.add(Implies(day == d, Or(
            start_time + 30 <= block_start,
            start_time >= block_end
        )))

# Add constraints for Sandra's availability
for d, blocks in sandra_busy.items():
    for block_start, block_end in blocks:
        s.add(Implies(day == d, Or(
            start_time + 30 <= block_start,
            start_time >= block_end
        )))

# Minimize day first, then start time
s.minimize(day * 1000 + start_time)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start_time].as_long()
    days = ["Monday", "Tuesday", "Wednesday"]
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")