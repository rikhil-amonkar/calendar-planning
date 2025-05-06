from z3 import Solver, Int, Or, sat

s = Solver()
start = Int('start')

# Meeting duration 30 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 450)  # 450 = 17:00 - 0:30

# Jacob's busy intervals (minutes since 9:00)
jacob_busy = [(270, 300), (330, 360)]
for s_start, s_end in jacob_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Diana's busy intervals
diana_busy = [(30, 60), (150, 180), (240, 270), (420, 450)]
for s_start, s_end in diana_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Adam's busy intervals
adam_busy = [(30, 90), (120, 210), (390, 420)]
for s_start, s_end in adam_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Angela's busy intervals
angela_busy = [(30, 60), (90, 180), (240, 390), (420, 450)]
for s_start, s_end in angela_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Dennis's busy intervals
dennis_busy = [(0, 30), (90, 150), (240, 360), (450, 480)]
for s_start, s_end in dennis_busy:
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