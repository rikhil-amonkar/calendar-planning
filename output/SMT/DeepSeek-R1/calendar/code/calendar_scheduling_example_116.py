from z3 import Solver, Int, Or, sat

s = Solver()
start = Int('start')

# Meeting duration is 30 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 450)  # 450 = 17:00 - 0:30

# Anna's preference: not before 14:30 (14:30 is 330 minutes after 9:00)
s.add(start >= 330)

# Adam's busy: 14:00-15:00 (300-360 minutes)
s.add(Or(start + 30 <= 300, start >= 360))

# John's busy intervals (in minutes)
john_busy = [(240, 270), (300, 330), (390, 420), (450, 480)]
for s_start, s_end in john_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Stephanie's busy intervals
steph_busy = [(30, 60), (90, 120), (150, 420), (450, 480)]
for s_start, s_end in steph_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Anna's busy intervals
anna_busy = [(30, 60), (180, 210), (240, 390), (450, 480)]
for s_start, s_end in anna_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

if s.check() == sat:
    m = s.model()
    start_min = m[start].as_long()
    hours = start_min // 60 + 9
    minutes = start_min % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")