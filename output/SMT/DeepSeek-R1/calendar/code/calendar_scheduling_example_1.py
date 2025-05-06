from z3 import *

s = Optimize()

start_time = Int('start_time')

# Basic constraints
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # Must end by 17:00 (480 minutes)

# Billy's preference: meeting ends by 15:00 (360 minutes)
s.add(start_time + 30 <= 360)

# Raymond's constraints (9:00-9:30, 11:30-12:00, 13:00-13:30, 15:00-15:30)
raymond_blocks = [(0, 30), (150, 180), (240, 270), (360, 390)]
for start, end in raymond_blocks:
    s.add(Or(start_time + 30 <= start, start_time >= end))

# Billy's constraints (10:00-10:30, 12:00-13:00, 16:30-17:00)
billy_blocks = [(60, 90), (180, 240), (450, 480)]
for start, end in billy_blocks:
    s.add(Or(start_time + 30 <= start, start_time >= end))

# Donald's constraints (9:00-9:30, 10:00-11:00, 12:00-13:00, 14:00-14:30, 16:00-17:00)
donald_blocks = [(0, 30), (60, 120), (180, 240), (300, 330), (420, 480)]
for start, end in donald_blocks:
    s.add(Or(start_time + 30 <= start, start_time >= end))

# Find earliest possible time
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