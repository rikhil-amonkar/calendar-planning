from z3 import *

s = Solver()

# Define the start time in minutes since midnight
start_time = Int('start_time')

# Meeting duration is 30 minutes
duration = 30

# Work hours are 9:00 (540) to 17:00 (1020)
s.add(start_time >= 540)
s.add(start_time + duration <= 1020)

# Lisa's busy periods: 10:30-11:00 (630-660), 11:30-12:00 (690-720), 14:00-15:00 (840-900)
s.add(Or(start_time + duration <= 630, start_time >= 660))  # Avoid 630-660
s.add(Or(start_time + duration <= 690, start_time >= 720))  # Avoid 690-720
s.add(Or(start_time + duration <= 840, start_time >= 900))  # Avoid 840-900

# Dorothy's preference: avoid after 10:30 (630) - meeting must end by 10:30
s.add(start_time + duration <= 630)

# Raymond's busy periods: 9:00-10:00 (540-600), 10:30-11:00 (630-660), 
# 11:30-15:00 (690-900), 16:00-17:00 (960-1020)
s.add(start_time >= 600)  # Must start after Raymond's 9:00-10:00 block
s.add(Or(start_time + duration <= 630, start_time >= 660))  # Avoid 630-660
s.add(Or(start_time + duration <= 690, start_time >= 900))  # Avoid 690-900
s.add(Or(start_time + duration <= 960, start_time >= 1020)) # Avoid 960-1020

if s.check() == sat:
    m = s.model()
    start = m[start_time].as_long()
    hours = start // 60
    minutes = start % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")