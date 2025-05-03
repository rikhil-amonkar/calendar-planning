from z3 import *

s = Solver()

# Define the start time in minutes since midnight
start_time = Int('start_time')

# Meeting duration is 30 minutes
duration = 30

# Work hours are 9:00 (540) to 17:00 (1020)
s.add(start_time >= 540)
s.add(start_time + duration <= 1020)

# Jeremy's busy periods: 12:00-13:00 (720-780), 13:30-14:00 (810-840), 15:00-15:30 (900-930)
s.add(Or(start_time + duration <= 720, start_time >= 780))  # Avoid 720-780
s.add(Or(start_time + duration <= 810, start_time >= 840))  # Avoid 810-840
s.add(Or(start_time + duration <= 900, start_time >= 930))  # Avoid 900-930

# Donna's busy periods: 9:30-10:00 (570-600), 13:00-13:30 (780-810), 16:00-17:00 (960-1020)
s.add(Or(start_time >= 600, start_time + duration <= 570))  # Avoid 570-600
s.add(Or(start_time >= 810, start_time + duration <= 780))  # Avoid 780-810
s.add(Or(start_time + duration <= 960, start_time >= 1020)) # Avoid 960-1020 (start_time >=1020 is impossible)

# Robert's busy periods: 9:00-11:00 (540-660), 11:30-12:00 (690-720), 12:30-17:00 (750-1020)
s.add(start_time >= 660)  # Must start after 660 (11:00)
s.add(Or(start_time + duration <= 690, start_time >= 720))  # Avoid 690-720
s.add(Or(start_time + duration <= 750, start_time >= 1020)) # Avoid 750-1020 (start_time >=1020 is impossible)

if s.check() == sat:
    m = s.model()
    start = m[start_time].as_long()
    hours = start // 60
    minutes = start % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")