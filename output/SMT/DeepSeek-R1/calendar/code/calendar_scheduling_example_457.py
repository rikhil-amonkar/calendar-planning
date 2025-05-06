from z3 import Solver, Int, Or, sat

s = Solver()
start = Int('start')

# Meeting duration 30 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 450)  # 450 = 17:00 - 0:30

# Andrea's busy intervals (minutes since 9:00)
andrea_busy = [(30, 90), (270, 330)]
for s_start, s_end in andrea_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Ruth's busy intervals
ruth_busy = [(210, 240), (360, 390)]
for s_start, s_end in ruth_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Steven's busy intervals
steven_busy = [(60, 90), (120, 150), (180, 210), (270, 300), (360, 420)]
for s_start, s_end in steven_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Kyle's busy intervals
kyle_busy = [(0, 30), (90, 180), (210, 240), (270, 420), (450, 480)]
for s_start, s_end in kyle_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Elijah's busy intervals
elijah_busy = [(0, 120), (150, 240), (270, 300), (390, 420), (450, 480)]
for s_start, s_end in elijah_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Lori's busy intervals
lori_busy = [(0, 30), (60, 150), (180, 270), (300, 420), (450, 480)]
for s_start, s_end in lori_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Grace has no constraints

# Find earliest possible time
s.minimize(start)

if s.check() == sat:
    m = s.model()
    start_min = m[start].as_long()
    hours = start_min // 60 + 9
    minutes = start_min % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")