from z3 import *

s = Solver()

# Define the start time in minutes since midnight
start_time = Int('start_time')

# Meeting duration is 60 minutes (1 hour)
duration = 60

# Work hours are 9:00 (540) to 17:00 (1020)
s.add(start_time >= 540)
s.add(start_time + duration <= 1020)

# Lisa's busy periods: 9:30-10:00 (570-600), 11:30-12:00 (690-720)
s.add(Or(start_time + duration <= 570, start_time >= 600))  # Avoid 570-600
s.add(Or(start_time + duration <= 690, start_time >= 720))  # Avoid 690-720

# Patrick's busy periods: 9:30-11:30 (570-690), 12:30-13:30 (750-810), 16:00-17:00 (960-1020)
s.add(Or(start_time + duration <= 570, start_time >= 690))  # Avoid 570-690
s.add(Or(start_time + duration <= 750, start_time >= 810))  # Avoid 750-810
s.add(Or(start_time + duration <= 960, start_time >= 1020)) # Avoid 960-1020

if s.check() == sat:
    m = s.model()
    start = m[start_time].as_long()
    hours = start // 60
    minutes = start % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")