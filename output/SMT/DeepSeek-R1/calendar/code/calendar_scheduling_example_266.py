from z3 import Solver, Int, Or, sat

s = Solver()
start = Int('start')

# Meeting duration 30 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 450)  # 450 = 17:00 - 0:30

# Joe's busy intervals (minutes since 9:00)
joe_busy = [(30, 60), (90, 120)]
for s_start, s_end in joe_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Keith's busy intervals
keith_busy = [(150, 180), (360, 390)]
for s_start, s_end in keith_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Patricia's busy intervals
patricia_busy = [(0, 30), (240, 270)]
for s_start, s_end in patricia_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Nancy's busy intervals
nancy_busy = [(0, 120), (150, 450)]
for s_start, s_end in nancy_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Pamela's busy intervals
pamela_busy = [(0, 60), (90, 120), (150, 180), (240, 300), (330, 360), (390, 420), (450, 480)]
for s_start, s_end in pamela_busy:
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