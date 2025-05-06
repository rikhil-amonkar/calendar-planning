from z3 import Solver, Int, Or, sat

s = Solver()
start = Int('start')

# Meeting duration 30 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 450)  # 450 = 17:00 - 0:30

# Margaret's busy intervals (minutes since 9:00)
margaret_busy = [(0, 60), (90, 120), (150, 180), (240, 270), (360, 390)]
for s_start, s_end in margaret_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Donna's busy intervals
donna_busy = [(330, 360), (420, 450)]
for s_start, s_end in donna_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Helen's busy intervals and preference (end by 13:30)
helen_busy = [(0, 30), (60, 150), (240, 300), (330, 360), (390, 480)]
for s_start, s_end in helen_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))
s.add(start + 30 <= 270)  # Must end by 13:30 (270 minutes)

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