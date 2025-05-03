from z3 import *

s = Solver()

# Define the start time in minutes since midnight
start_time = Int('start_time')

# Meeting duration is 30 minutes
duration = 30

# Work hours are 9:00 (540) to 17:00 (1020)
s.add(start_time >= 540)
s.add(start_time + duration <= 1020)

# Virginia's busy periods: 10:00-12:00 (600-720)
s.add(Or(start_time + duration <= 600, start_time >= 720))

# Charles' constraints:
# Busy periods: 12:00-12:30 (720-750), 13:00-13:30 (780-810)
s.add(Or(start_time + duration <= 720, start_time >= 750))  # Avoid 720-750
s.add(Or(start_time + duration <= 780, start_time >= 810))  # Avoid 780-810
# Preference: avoid before 14:30 (870)
s.add(start_time >= 870)

# Megan's busy periods: 9:00-12:00 (540-720), 13:30-16:00 (810-960), 16:30-17:00 (990-1020)
s.add(Or(start_time + duration <= 540, start_time >= 720))   # Avoid 540-720
s.add(Or(start_time + duration <= 810, start_time >= 960))   # Avoid 810-960
s.add(Or(start_time + duration <= 990, start_time >= 1020))  # Avoid 990-1020

if s.check() == sat:
    m = s.model()
    start = m[start_time].as_long()
    hours = start // 60
    minutes = start % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")