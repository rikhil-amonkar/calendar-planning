from z3 import Solver, Int, Or, sat

s = Solver()
start = Int('start')

# Meeting duration 30 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 450)  # 450 = 17:00 - 0:30

# Christine's busy intervals (minutes since 9:00)
christine_busy = [(30, 90), (180, 210), (240, 270), (330, 360), (420, 450)]
for s_start, s_end in christine_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Bobby's busy intervals
bobby_busy = [(180, 210), (330, 360)]
for s_start, s_end in bobby_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Elizabeth's busy intervals
elizabeth_busy = [(0, 30), (150, 240), (270, 300), (360, 390), (420, 480)]
for s_start, s_end in elizabeth_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Tyler's busy intervals
tyler_busy = [(0, 120), (180, 210), (240, 270), (390, 420), (450, 480)]
for s_start, s_end in tyler_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Edward's busy intervals
edward_busy = [(0, 30), (60, 120), (150, 300), (330, 390), (420, 480)]
for s_start, s_end in edward_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Janice's preference: meeting ends by 13:00 (start +30 <= 240)
s.add(start + 30 <= 240)

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