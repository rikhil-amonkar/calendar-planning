from z3 import *

s = Optimize()

start_time = Int('start_time')

# Time constraints (minutes since 9:00)
s.add(start_time >= 300)  # David's constraint: no meetings before 14:00 (300 minutes)
s.add(start_time + 30 <= 480)  # 30-minute duration

# Define busy blocks in minutes since 9:00 (Monday only)
busy = {
    'David': [(150, 180), (330, 360)],
    'Douglas': [(30, 60), (150, 180), (240, 270), (330, 360)],
    'Ralph': [(0, 30), (60, 120), (150, 210), (270, 360), (390, 420), (450, 480)],
    'Jordan': [(0, 60), (180, 210), (240, 270), (330, 360), (390, 480)]
}

# Add constraints for each participant's busy times (Natalie has none)
for person, blocks in busy.items():
    for block_start, block_end in blocks:
        s.add(Or(
            start_time + 30 <= block_start,
            start_time >= block_end
        ))

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