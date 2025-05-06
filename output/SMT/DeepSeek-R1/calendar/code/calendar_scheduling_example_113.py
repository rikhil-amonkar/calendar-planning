from z3 import Solver, Int, Or, sat

s = Solver()
start = Int('start')

# Meeting duration 30 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 450)  # 450 = 17:00 - 0:30

# Bradley's busy intervals (minutes since 9:00)
bradley_busy = [(30, 60), (150, 180), (210, 240), (390, 420)]
for s_start, s_end in bradley_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Teresa's busy intervals
teresa_busy = [(90, 120), (180, 210), (240, 270), (330, 360)]
for s_start, s_end in teresa_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Elizabeth's busy intervals
elizabeth_busy = [(0, 30), (90, 150), (240, 270), (330, 360), (390, 480)]
for s_start, s_end in elizabeth_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Christian's busy intervals
christian_busy = [(0, 30), (90, 480)]
for s_start, s_end in christian_busy:
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