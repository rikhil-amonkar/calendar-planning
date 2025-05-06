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

# Ronald's busy blocks (converted to minutes since 9:00)
ronald_busy = {
    0: [(90, 120), (180, 210), (390, 420)],  # Monday
    1: [(0, 30), (180, 210), (390, 450)],    # Tuesday
    2: [(30, 90), (120, 180), (210, 240), (270, 300), (450, 480)]  # Wednesday
}

# Amber's busy blocks
amber_busy = {
    0: [(0, 30), (60, 90), (150, 180), (210, 300), (330, 360), (390, 480)],  # Monday
    1: [(0, 30), (60, 150), (180, 210), (270, 390), (450, 480)],             # Tuesday
    2: [(0, 30), (60, 90), (120, 270), (360, 390)]                          # Wednesday
}

# Add constraints for Ronald's availability
for d, blocks in ronald_busy.items():
    for block_start, block_end in blocks:
        s.add(Implies(day == d, Or(
            start_time + 30 <= block_start,
            start_time >= block_end
        )))

# Add constraints for Amber's availability
for d, blocks in amber_busy.items():
    for block_start, block_end in blocks:
        s.add(Implies(day == d, Or(
            start_time + 30 <= block_start,
            start_time >= block_end
        )))

# Optimize for earliest possible time (day first, then start time)
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