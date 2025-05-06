from z3 import Solver, Int, Or, sat

s = Solver()
start = Int('start')

# Meeting duration 30 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 450)  # 450 = 17:00 - 0:30

# Shirley's busy intervals (minutes since 9:00)
shirley_busy = [(90, 120), (180, 210)]
for s_start, s_end in shirley_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Jacob's busy intervals
jacob_busy = [(0, 30), (60, 90), (120, 150), (210, 270), (330, 360)]
for s_start, s_end in jacob_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Stephen's busy intervals
stephen_busy = [(150, 180), (210, 240)]
for s_start, s_end in stephen_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Margaret's busy intervals and preference (start >= 14:30)
margaret_busy = [(0, 30), (90, 210), (240, 270), (360, 390), (450, 480)]
for s_start, s_end in margaret_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))
s.add(start >= 330)  # 14:30 = 330 minutes

# Mason's busy intervals
mason_busy = [(0, 60), (90, 120), (150, 210), (240, 270), (300, 330), (450, 480)]
for s_start, s_end in mason_busy:
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