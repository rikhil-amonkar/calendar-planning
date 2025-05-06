from z3 import *

s = Optimize()

start_time = Int('start_time')

# Basic constraints
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # 9:00-17:00 (480 minutes)

# Cynthia's constraints (9:30-10:30, 11:30-12:00, 13:00-13:30, 15:00-16:00)
cynthia_blocks = [(30, 90), (150, 180), (240, 270), (360, 420)]
for start, end in cynthia_blocks:
    s.add(Or(start_time + 30 <= start, start_time >= end))

# Lauren's constraints (9:00-9:30, 10:30-11:00, 11:30-12:00, 13:00-13:30, 14:00-14:30, 15:00-15:30, 16:00-17:00)
lauren_blocks = [(0, 30), (90, 120), (150, 180), (240, 270), (300, 330), (360, 390), (420, 480)]
for start, end in lauren_blocks:
    s.add(Or(start_time + 30 <= start, start_time >= end))

# Robert's constraints (10:30-11:00, 11:30-12:00, 12:30-13:30, 14:00-16:00)
robert_blocks = [(90, 120), (150, 180), (210, 270), (300, 420)]
for start, end in robert_blocks:
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