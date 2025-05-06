from z3 import *

s = Optimize()

day = Int('day')
start_time = Int('start_time')

# Day constraints (0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday)
s.add(Or(day == 2, day == 4))  # Only Wednesday or Friday allowed based on preferences

# Basic time constraints (minutes since 9:00)
s.add(start_time >= 0)
s.add(start_time + 60 <= 480)  # 1-hour duration

# Bryan's busy blocks (only Friday has meetings)
bryan_busy = {
    4: [(90, 120), (300, 330)]  # Friday blocks
}

# Nicholas's busy blocks for Wednesday and Friday
nicholas_busy = {
    2: [(0, 30), (60, 120), (150, 270), (300, 330), (360, 450)],  # Wednesday
    4: [(0, 90), (120, 180), (210, 330), (390, 420), (450, 480)]  # Friday
}

# Add constraints for Bryan's availability
for d, blocks in bryan_busy.items():
    for block_start, block_end in blocks:
        s.add(Implies(day == d, Or(
            start_time + 60 <= block_start,
            start_time >= block_end
        )))

# Add constraints for Nicholas's availability
for d, blocks in nicholas_busy.items():
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
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 60) // 60
    end_m = (st + 60) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")