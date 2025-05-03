from z3 import *

# Initialize solver
s = Solver()

# Meeting start time in minutes after 9:00 (0 = 9:00)
S = Int('S')
work_end = 480  # 17:00 (8 hours after 9:00)
meeting_duration = 60

s.add(S >= 0, S <= work_end - meeting_duration)  # Must end by 17:00

# Convert blocked times to minutes since 9:00
arthur_busy = [(0, 30), (90, 180), (420, 480)]        # 9-9:30, 10:30-12:00, 16-17
michael_busy = [(240, 270), (300, 330)]               # 13-13:30, 14-14:30
samantha_busy = [(90, 120), (180, 360), (390, 480)]   # 10:30-11, 12-15, 15:30-17

# Add constraints for each person's schedule
for start, end in arthur_busy:
    s.add(Or(S + meeting_duration <= start, S >= end))
for start, end in michael_busy:
    s.add(Or(S + meeting_duration <= start, S >= end))
for start, end in samantha_busy:
    s.add(Or(S + meeting_duration <= start, S >= end))

# Find earliest valid time
if s.check() == sat:
    m = s.model()
    start_min = m[S].as_long()
    # Convert to HH:MM format
    print(f"{(9 + start_min // 60):02d}:{(start_min % 60):02d}")
else:
    print("No valid time found")