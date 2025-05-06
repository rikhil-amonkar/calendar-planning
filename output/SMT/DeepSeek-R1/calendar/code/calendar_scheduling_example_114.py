from z3 import Solver, Int, Or, sat

s = Solver()
start = Int('start')

# Meeting duration 60 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 420)  # 420 = 17:00 - 1:00

# Stephanie's busy intervals (minutes since 9:00)
stephanie_busy = [(60, 90), (420, 450)]
for s_start, s_end in stephanie_busy:
    s.add(Or(start + 60 <= s_start, start >= s_end))

# Cheryl's busy intervals
cheryl_busy = [(60, 90), (150, 180), (270, 300), (450, 480)]
for s_start, s_end in cheryl_busy:
    s.add(Or(start + 60 <= s_start, start >= s_end))

# Bradley's busy intervals
bradley_busy = [(30, 60), (90, 150), (270, 300), (330, 360), (390, 480)]
for s_start, s_end in bradley_busy:
    s.add(Or(start + 60 <= s_start, start >= s_end))

# Steven's busy intervals
steven_busy = [(0, 180), (240, 270), (330, 480)]
for s_start, s_end in steven_busy:
    s.add(Or(start + 60 <= s_start, start >= s_end))

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