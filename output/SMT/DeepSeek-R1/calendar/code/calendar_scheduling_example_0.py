from z3 import *

# Initialize solver
s = Solver()

# Meeting start time in minutes after 9:00
S = Int('S')
min_time = 0  # 9:00
max_time = 420  # 16:00 (since meeting lasts 1 hour, must end by 17:00)

s.add(S >= min_time, S <= max_time)

# Michelle's blocked intervals (11:00-12:00 → 120-180 minutes)
michelle = [(120, 180)]
# Steven's blocked intervals
steven = [(0, 30), (150, 180), (270, 300), (390, 420)]
# Jerry's blocked intervals
jerry = [(0, 30), (60, 120), (150, 210), (240, 330), (390, 420), (450, 480)]

# Add constraints for each person's blocked times
for start, end in michelle:
    s.add(Or(S + 60 <= start, S >= end))
for start, end in steven:
    s.add(Or(S + 60 <= start, S >= end))
for start, end in jerry:
    s.add(Or(S + 60 <= start, S >= end))

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