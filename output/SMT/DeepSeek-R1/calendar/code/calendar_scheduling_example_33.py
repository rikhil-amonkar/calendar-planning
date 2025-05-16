from z3 import *

s = Solver()

start = Int('start')
duration = 30  # Meeting duration in minutes

# Convert times to minutes since 9:00 (9:00 = 0, 17:00 = 480)
s.add(start >= 0)
s.add(start + duration <= 360)  # Must end by 15:00 due to Bobby's preference

# Lisa's blocked intervals (minutes from 9:00)
lisa_blocked = [(0, 60), (90, 150), (210, 240), (420, 450)]
for b_start, b_end in lisa_blocked:
    s.add(Or(start + duration <= b_start, start >= b_end))

# Bobby's blocked intervals
bobby_blocked = [(0, 30), (60, 90), (150, 180), (360, 390)]
for b_start, b_end in bobby_blocked:
    s.add(Or(start + duration <= b_start, start >= b_end))

# Randy's blocked intervals
randy_blocked = [(30, 60), (90, 120), (150, 210), (240, 270), (330, 390), (420, 450)]
for b_start, b_end in randy_blocked:
    s.add(Or(start + duration <= b_start, start >= b_end))

if s.check() == sat:
    m = s.model()
    start_val = m[start].as_long()
    hours = 9 + start_val // 60
    minutes = start_val % 60
    end_val = start_val + duration
    end_h = 9 + end_val // 60
    end_m = end_val % 60
    print(f"Monday {hours:02d}:{minutes:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No valid slot found")