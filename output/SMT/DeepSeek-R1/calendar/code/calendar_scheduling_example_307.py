from z3 import *

s = Optimize()

start_time = Int('start_time')

# Fixed to Monday (no day variable needed)
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # 30-minute duration

# Define busy blocks in minutes since 9:00 (Monday only)
busy = {
    'Stephen': [(60, 90), (180, 210)],
    'Brittany': [(120, 150), (270, 300), (390, 420), (450, 480)],
    'Dorothy': [(0, 30), (60, 90), (120, 210), (240, 360), (390, 480)],
    'Rebecca': [(30, 90), (120, 150), (180, 210), (240, 480)],
    'Jordan': [(0, 30), (60, 120), (150, 180), (240, 360), (390, 420)]
}

# Add constraints for each participant's busy times
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