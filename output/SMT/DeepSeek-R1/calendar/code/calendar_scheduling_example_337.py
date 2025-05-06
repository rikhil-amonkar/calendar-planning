from z3 import *

s = Optimize()

start_time = Int('start_time')
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # 30-minute duration

# Convert schedules to minutes since 9:00
busy = {
    'John': [(150, 180), (300, 330)],
    'Megan': [(180, 210), (300, 360), (390, 420)],
    'Kimberly': [(0, 30), (60, 90), (120, 330), (360, 420), (450, 480)],
    'Sean': [(60, 120), (150, 300), (360, 390)],
    'Lori': [(0, 30), (90, 180), (240, 330), (420, 450)],
}

# Brandon has no meetings, so no constraints

for person, blocks in busy.items():
    for block_start, block_end in blocks:
        s.add(Or(start_time + 30 <= block_start, start_time >= block_end))

# Optimize for earliest time
s.minimize(start_time)

if s.check() == sat:
    m = s.model()
    st = m[start_time].as_long()
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")