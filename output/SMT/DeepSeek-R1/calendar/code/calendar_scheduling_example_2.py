from z3 import *

# Initialize solver
s = Solver()

# Meeting start time in minutes after 9:00
S = Int('S')
min_time = 0  # 9:00
max_time = 360  # Must end by 15:30 (390 min) → S <= 360

s.add(S >= min_time, S <= max_time)

# Roy's blocked intervals (converted to minutes)
roy = [(0, 30), (60, 90), (120, 150), (210, 240)]
# Kathryn's blocked intervals
kathryn = [(30, 60), (450, 480)]
# Amy's blocked intervals
amy = [(0, 330), (360, 420), (450, 480)]

# Add constraints for each person's blocked times
for start, end in roy:
    s.add(Or(S + 30 <= start, S >= end))
for start, end in kathryn:
    s.add(Or(S + 30 <= start, S >= end))
for start, end in amy:
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