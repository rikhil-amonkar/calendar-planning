from z3 import Solver, Int, Or, sat

s = Solver()
start = Int('start')

# Meeting duration 30 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 450)  # 450 = 17:00 - 0:30

# Jose's constraint: meeting can't start after 15:30 (360 minutes)
s.add(start <= 360)

# Jose's busy intervals (minutes since 9:00)
jose_busy = [(120, 150), (210, 240)]
for s_start, s_end in jose_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Keith's busy intervals
keith_busy = [(300, 330), (360, 390)]
for s_start, s_end in keith_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Logan's busy intervals
logan_busy = [(0, 60), (180, 210), (360, 390)]
for s_start, s_end in logan_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Megan's busy intervals
megan_busy = [(0, 90), (120, 180), (240, 270), (330, 450)]
for s_start, s_end in megan_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Gary's busy intervals
gary_busy = [(0, 30), (60, 90), (150, 240), (270, 300), (330, 450)]
for s_start, s_end in gary_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Bobby's busy intervals
bobby_busy = [(120, 150), (180, 210), (240, 420)]
for s_start, s_end in bobby_busy:
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