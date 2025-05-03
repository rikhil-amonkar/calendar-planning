from z3 import *

s = Solver()

# Define the start time in minutes since midnight
start_time = Int('start_time')

# Meeting duration is 30 minutes
duration = 30

# Work hours are 9:00 (540) to 17:00 (1020)
s.add(start_time >= 540)
s.add(start_time + duration <= 1020)

# Jeffrey's preference: avoid meetings before 14:00 (840)
s.add(start_time >= 840)

# Jack's busy periods: 10:30-11:30 (630-690), 13:00-13:30 (780-810), 14:00-14:30 (840-870), 16:00-17:00 (960-1020)
s.add(Or(start_time + duration <= 630, start_time >= 690))  # Avoid 630-690
s.add(Or(start_time + duration <= 780, start_time >= 810))  # Avoid 780-810
s.add(Or(start_time + duration <= 840, start_time >= 870))  # Avoid 840-870
s.add(Or(start_time + duration <= 960, start_time >= 1020)) # Avoid 960-1020

# Judith's busy periods: 9:00-10:00 (540-600), 10:30-11:00 (630-660), 11:30-14:00 (690-840), 14:30-15:00 (870-900), 15:30-17:00 (930-1020)
s.add(Or(start_time + duration <= 540, start_time >= 600))  # Avoid 540-600
s.add(Or(start_time + duration <= 630, start_time >= 660))  # Avoid 630-660
s.add(Or(start_time + duration <= 690, start_time >= 840))  # Avoid 690-840
s.add(Or(start_time + duration <= 870, start_time >= 900))  # Avoid 870-900
s.add(Or(start_time + duration <= 930, start_time >= 1020)) # Avoid 930-1020

if s.check() == sat:
    m = s.model()
    start = m[start_time].as_long()
    hours = start // 60
    minutes = start % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")