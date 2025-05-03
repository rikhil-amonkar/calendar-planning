from z3 import *

# Initialize solver
s = Solver()

# Meeting start time in minutes after 9:00
S = Int('S')
min_time = 0  # 9:00
max_time = 330  # Must end by 15:00 (360 min) → S <= 330

s.add(S >= min_time, S <= max_time)

# Raymond's blocked intervals (converted to minutes)
raymond = [(0, 30), (150, 180), (240, 270), (360, 390)]
# Billy's blocked intervals
billy = [(60, 90), (180, 240), (450, 480)]
# Donald's blocked intervals
donald = [(0, 30), (60, 120), (180, 240), (300, 330), (420, 480)]

# Add constraints for each person's blocked times
for start, end in raymond:
    s.add(Or(S + 30 <= start, S >= end))
for start, end in billy:
    s.add(Or(S + 30 <= start, S >= end))
for start, end in donald:
    s.add(Or(S + 30 <= start, S >= end))

# Check for a solution
if s.check() == sat:
    m = s.model()
    start_time = m[S].as_long()
    # Convert minutes to time string
    hours = 9 + start_time // 60
    minutes = start_time % 60
    print(f"{hours:02d}:{minutes:02d}")
else:
    print("No valid time found")