from z3 import *

s = Solver()

# Define the start time in minutes since midnight
start_time = Int('start_time')

# Meeting duration is 60 minutes (1 hour)
duration = 60

# Work hours are 9:00 (540) to 17:00 (1020)
s.add(start_time >= 540)
s.add(start_time + duration <= 1020)

# Judith's busy periods: 10:00-10:30 (600-630), 11:00-12:00 (660-720), 12:30-13:00 (750-780)
s.add(Or(start_time + duration <= 600, start_time >= 630))  # Avoid 600-630
s.add(Or(start_time + duration <= 660, start_time >= 720))  # Avoid 660-720
s.add(Or(start_time + duration <= 750, start_time >= 780))  # Avoid 750-780

# Roger's busy periods: 9:00-9:30 (540-570), 10:30-11:00 (630-660), 
# 12:00-12:30 (720-750), 13:00-13:30 (780-810), 14:00-16:00 (840-960)
s.add(Or(start_time + duration <= 540, start_time >= 570))  # Avoid 540-570
s.add(Or(start_time + duration <= 630, start_time >= 660))  # Avoid 630-660
s.add(Or(start_time + duration <= 720, start_time >= 750))  # Avoid 720-750
s.add(Or(start_time + duration <= 780, start_time >= 810))  # Avoid 780-810
s.add(Or(start_time + duration <= 840, start_time >= 960))  # Avoid 840-960

# Madison has no constraints

if s.check() == sat:
    m = s.model()
    start = m[start_time].as_long()
    hours = start // 60
    minutes = start % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")