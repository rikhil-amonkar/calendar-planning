from z3 import *

s = Solver()

# Meeting start time in minutes after 9:00 (0 = 9:00)
S = Int('S')
meeting_duration = 60
max_start = 420  # 16:00 (17:00 - 1 hour)

# Convert blocked times to minutes since 9:00
dylan_busy = [(90, 120), (210, 240)]
jerry_busy = [(0, 120), (150, 330), (420, 480)]

# Base constraints: valid work hours
s.add(S >= 0, S <= max_start)

# Add schedule constraints for Dylan and Jerry
for start, end in dylan_busy:
    s.add(Or(S + meeting_duration <= start, S >= end))
for start, end in jerry_busy:
    s.add(Or(S + meeting_duration <= start, S >= end))

# Find earliest valid time
if s.check() == sat:
    m = s.model()
    start_min = m[S].as_long()
    print(f"{(9 + start_min // 60):02d}:{(start_min % 60):02d}")
else:
    print("No valid time found")