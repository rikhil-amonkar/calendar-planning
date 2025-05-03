from z3 import *

s = Solver()

# Meeting start time in minutes after 9:00
S = Int('S')
meeting_duration = 30
max_start = 450  # 16:30 (17:00 - 30 minutes)

# Convert blocked times to minutes since 9:00
heather_busy = [(0, 30), (90, 120), (240, 300), (330, 360), (420, 450)]
zachary_busy = [(0, 90), (120, 180), (210, 240), (270, 450)]

# Base constraints: valid work hours
s.add(S >= 0, S <= max_start)

# Zachary's preference: schedule before 14:00 (S + 30 <= 300)
s.add(S + meeting_duration <= 300)

# Add schedule constraints for Heather and Zachary
for start, end in heather_busy:
    s.add(Or(S + meeting_duration <= start, S >= end))
for start, end in zachary_busy:
    s.add(Or(S + meeting_duration <= start, S >= end))

# Check solution with preference first
if s.check() == sat:
    m = s.model()
    start_min = m[S].as_long()
else:
    # Retry without preference
    s = Solver()
    s.add(S >= 0, S <= max_start)
    for start, end in heather_busy:
        s.add(Or(S + meeting_duration <= start, S >= end))
    for start, end in zachary_busy:
        s.add(Or(S + meeting_duration <= start, S >= end))
    s.check()
    m = s.model()
    start_min = m[S].as_long()

# Format and print the time
hours = 9 + start_min // 60
minutes = start_min % 60
print(f"{hours:02d}:{minutes:02d}")