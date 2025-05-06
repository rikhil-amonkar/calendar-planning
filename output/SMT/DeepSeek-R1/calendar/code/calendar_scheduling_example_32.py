from z3 import Solver, Int, Or, sat

s = Solver()
start = Int('start')

# Meeting duration 30 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 450)  # 450 = 17:00 - 0:30

# Frank's preference: meeting must end by 9:30 (30 minutes after 9:00)
s.add(start + 30 <= 30)  # Forces start=0 (9:00-9:30)

# Emily's busy intervals (minutes since 9:00)
emily_busy = [(60, 90), (150, 180), (300, 360), (420, 450)]
for s_start, s_end in emily_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Melissa's busy intervals
melissa_busy = [(30, 60), (330, 360)]
for s_start, s_end in melissa_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Frank's busy intervals
frank_busy = [(60, 90), (120, 150), (210, 240), (270, 330), (360, 420), (450, 480)]
for s_start, s_end in frank_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

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