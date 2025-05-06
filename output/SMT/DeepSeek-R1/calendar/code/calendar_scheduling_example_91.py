from z3 import Solver, Int, Or, sat

s = Solver()
start = Int('start')

# Meeting duration 60 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 420)  # 420 = 17:00 - 1:00

# Danielle's busy intervals (minutes since 9:00)
danielle_busy = [(0, 60), (90, 120), (330, 360), (390, 420), (450, 480)]
for s_start, s_end in danielle_busy:
    s.add(Or(start + 60 <= s_start, start >= s_end))

# Bruce's busy intervals
bruce_busy = [(120, 150), (210, 240), (300, 330), (390, 420)]
for s_start, s_end in bruce_busy:
    s.add(Or(start + 60 <= s_start, start >= s_end))

# Eric's busy intervals
eric_busy = [(0, 30), (60, 120), (150, 240), (330, 390)]
for s_start, s_end in eric_busy:
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