from z3 import *

# Initialize solver
s = Solver()

# Meeting start time in minutes after 9:00 (0 = 9:00)
S = Int('S')
work_end = 480  # 17:00 (8 hours after 9:00)
meeting_duration = 30

# Must end by 17:00
s.add(S >= 0, S <= work_end - meeting_duration)

# Convert blocked times to minutes since 9:00
donna_busy = [(300, 330), (390, 420)]          # 14:00-14:30, 15:30-16:00
john_busy = [(120, 150), (450, 480)]           # 11:00-11:30, 16:30-17:00
billy_busy = [(0, 60), (90, 300), (330, 480)]  # 9:00-10:00, 10:30-14:00, 14:30-17:00

# Add constraints for each person's schedule
for start, end in donna_busy:
    s.add(Or(S + meeting_duration <= start, S >= end))
for start, end in john_busy:
    s.add(Or(S + meeting_duration <= start, S >= end))
for start, end in billy_busy:
    s.add(Or(S + meeting_duration <= start, S >= end))

# Find earliest valid time
if s.check() == sat:
    m = s.model()
    start_min = m[S].as_long()
    # Convert to HH:MM format
    print(f"{(9 + start_min // 60):02d}:{(start_min % 60):02d}")
else:
    print("No valid time found")