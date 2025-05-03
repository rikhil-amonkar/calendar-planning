from z3 import *

s = Solver()

# Define the start time in minutes since midnight
start_time = Int('start_time')

# Meeting duration is 60 minutes (1 hour)
duration = 60

# Work hours are 9:00 (540) to 17:00 (1020)
s.add(start_time >= 540)
s.add(start_time + duration <= 1020)

# Sharon's blocked periods: 9:00-13:00 (540-780), 14:00-17:00 (840-1020)
# Available window: 13:00-14:00 (780-840)
s.add(start_time >= 780)          # Must start after 13:00
s.add(start_time + duration <= 840)  # Must end by 14:00

# Abigail and Michael have no constraints

if s.check() == sat:
    m = s.model()
    start = m[start_time].as_long()
    hours = start // 60
    minutes = start % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")