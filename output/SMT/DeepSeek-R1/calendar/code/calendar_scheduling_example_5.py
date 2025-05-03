from z3 import *

# Initialize solver
s = Solver()

# Meeting start time in minutes after 9:00 (0 = 9:00)
S = Int('S')
meeting_duration = 30
latest_start = 240  # 13:00 (since meeting must end by 13:30)

# Convert blocked times to minutes since 9:00
kathryn_busy = [(0, 30), (90, 120), (150, 180)]
charlotte_busy = [(180, 210)]
lauren_busy = [(0, 60), (180, 210)]

# Base constraints: valid work hours and Charlotte's preference
s.add(S >= 0, S <= latest_start - meeting_duration)

# Add schedule constraints for each participant
for start, end in kathryn_busy:
    s.add(Or(S + meeting_duration <= start, S >= end))
for start, end in charlotte_busy:
    s.add(Or(S + meeting_duration <= start, S >= end))
for start, end in lauren_busy:
    s.add(Or(S + meeting_duration <= start, S >= end))

# Find earliest valid time
if s.check() == sat:
    m = s.model()
    start_min = m[S].as_long()
    print(f"{(9 + start_min // 60):02d}:{(start_min % 60):02d}")
else:
    print("No valid time found")