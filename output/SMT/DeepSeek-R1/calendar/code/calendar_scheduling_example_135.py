from z3 import *

s = Optimize()

start_time = Int('start_time')

# Basic constraints
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # 9:00-17:00 (480 minutes)

# Ashley's constraints (10:00-10:30, 11:00-12:00, 12:30-13:00, 15:00-16:00)
ashley_blocks = [(60, 90), (120, 180), (210, 240), (360, 420)]
for start, end in ashley_blocks:
    s.add(Or(start_time + 30 <= start, start_time >= end))

# Ronald's constraints (9:00-9:30, 10:00-11:30, 12:30-14:00, 14:30-17:00)
ronald_blocks = [(0, 30), (60, 150), (210, 300), (330, 480)]
for start, end in ronald_blocks:
    s.add(Or(start_time + 30 <= start, start_time >= end))

# Larry's constraints (9:00-12:00, 13:00-17:00)
larry_blocks = [(0, 180), (240, 480)]
for start, end in larry_blocks:
    s.add(Or(start_time + 30 <= start, start_time >= end))

# Minimize start time for earliest availability
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