from z3 import *

s = Optimize()

start_time = Int('start_time')

# Basic constraints (work hours 9:00-17:00 = 0-480 minutes)
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)

# Bobby's preference: meeting ends by 15:00 (360 minutes)
s.add(start_time + 30 <= 360)

# Lisa's blocked times (minutes since 9:00)
lisa_blocks = [(0, 60), (90, 150), (150, 180), (420, 450)]
for start, end in lisa_blocks:
    s.add(Or(start_time + 30 <= start, start_time >= end))

# Bobby's blocked times
bobby_blocks = [(0, 30), (60, 90), (150, 180), (360, 390)]
for start, end in bobby_blocks:
    s.add(Or(start_time + 30 <= start, start_time >= end))

# Randy's blocked times
randy_blocks = [(30, 60), (90, 120), (150, 210), (240, 270), (330, 390), (420, 450)]
for start, end in randy_blocks:
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