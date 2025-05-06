from z3 import *

s = Optimize()

day = Int('day')
start_time = Int('start_time')

# Day can be Monday (0) or Tuesday (1)
s.add(Or(day == 0, day == 1))

# Basic time constraints (minutes since 9:00)
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # Half-hour duration

# Define busy blocks for each participant (Monday only)
busy = {
    'Jacqueline': {0: [(0, 30), (120, 150), (210, 240), (390, 420)]},
    'Harold': {0: [(60, 90), (240, 270), (360, 480)]},
    'Arthur': {0: [(0, 30), (60, 210), (330, 360), (390, 480)]},
    'Kelly': {0: [(0, 30), (60, 120), (150, 180), (300, 360), (390, 420)]}
}

# Harold's preference: No meetings on Monday after 13:00 (240 minutes)
s.add(Implies(day == 0, start_time + 30 <= 240))

# Add constraints for each participant's busy times
for person, schedule in busy.items():
    for d, blocks in schedule.items():
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
    days = ["Monday", "Tuesday"]
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")