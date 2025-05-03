from z3 import *

s = Solver()

# Define the start time in minutes since midnight
start_time = Int('start_time')

# Meeting duration is 60 minutes (1 hour)
duration = 60

# Work hours are 9:00 (540) to 17:00 (1020)
s.add(start_time >= 540)
s.add(start_time + duration <= 1020)

# Keith's busy periods: 14:00-14:30 (840-870), 16:00-16:30 (960-990)
s.add(Or(start_time + duration <= 840, start_time >= 870))
s.add(Or(start_time + duration <= 960, start_time >= 990))

# Cynthia's busy periods: 9:00-10:30 (540-630), 11:30-17:00 (690-1020)
s.add(Or(start_time + duration <= 540, start_time >= 630))
s.add(Or(start_time + duration <= 690, start_time >= 1020))

# Christine has no busy periods, so no constraints

if s.check() == sat:
    m = s.model()
    start = m[start_time].as_long()
    hours = start // 60
    minutes = start % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")