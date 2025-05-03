from z3 import *

s = Solver()

# Define the start time in minutes since midnight
start_time = Int('start_time')

# Meeting duration is 60 minutes (1 hour)
duration = 60

# Work hours are 9:00 (540) to 17:00 (1020)
s.add(start_time >= 540)
s.add(start_time + duration <= 1020)

# Nancy's busy periods: 9:30-10:00 (570-600), 12:30-13:00 (750-780)
s.add(Or(start_time + duration <= 570, start_time >= 600))  # Avoid 570-600
s.add(Or(start_time + duration <= 750, start_time >= 780))  # Avoid 750-780

# Nathan's busy periods: 9:00-12:30 (540-750), 13:00-14:30 (780-870), 16:00-17:00 (960-1020)
s.add(Or(start_time + duration <= 540, start_time >= 750))  # Avoid 540-750
s.add(Or(start_time + duration <= 780, start_time >= 870))  # Avoid 780-870
s.add(Or(start_time + duration <= 960, start_time >= 1020)) # Avoid 960-1020

# Albert has no constraints

if s.check() == sat:
    m = s.model()
    start = m[start_time].as_long()
    hours = start // 60
    minutes = start % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")