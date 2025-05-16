from z3 import *

s = Solver()

start = Int('start')
duration = 30  # Meeting duration in minutes

# Convert all times to minutes since 9:00
s.add(start >= 0)  # Meeting can't start before 9:00
s.add(start + duration <= 360)  # Must end by 15:00 (360 minutes from 9:00)

# Raymond's blocked intervals (minutes from 9:00)
raymond_blocked = [(0, 30), (150, 180), (240, 270), (360, 390)]
for b_start, b_end in raymond_blocked:
    s.add(Or(start + duration <= b_start, start >= b_end))

# Billy's blocked intervals
billy_blocked = [(60, 90), (180, 240), (450, 480)]
for b_start, b_end in billy_blocked:
    s.add(Or(start + duration <= b_start, start >= b_end))

# Donald's blocked intervals
donald_blocked = [(0, 30), (60, 120), (180, 240), (300, 330), (420, 480)]
for b_start, b_end in donald_blocked:
    s.add(Or(start + duration <= b_start, start >= b_end))

if s.check() == sat:
    m = s.model()
    start_val = m[start].as_long()
    # Convert start time to HH:MM format
    hours = 9 + start_val // 60
    minutes = start_val % 60
    end_val = start_val + duration
    end_h = 9 + end_val // 60
    end_m = end_val % 60
    print(f"Monday {hours:02d}:{minutes:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No valid slot found")