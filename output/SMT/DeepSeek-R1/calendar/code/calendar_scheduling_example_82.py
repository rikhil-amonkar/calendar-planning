from z3 import Solver, Int, Or, sat

s = Solver()
start = Int('start')

# Meeting duration 30 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 450)  # 450 = 17:00 - 0:30

# Michael's busy intervals (minutes since 9:00)
michael_busy = [(30, 90), (360, 390), (420, 450)]
for s_start, s_end in michael_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Arthur's busy intervals
arthur_busy = [(0, 180), (240, 360), (390, 420), (450, 480)]
for s_start, s_end in arthur_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Eric has no constraints

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