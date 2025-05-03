from z3 import *

s = Solver()

# Define the start time in minutes since midnight
start_time = Int('start_time')

# Meeting duration is 60 minutes (1 hour)
duration = 60

# Work hours are 9:00 (540) to 17:00 (1020)
s.add(start_time >= 540)
s.add(start_time + duration <= 1020)

# Joan's busy periods: 11:00-11:30 (660-690), 12:30-13:00 (750-780)
s.add(Or(start_time + duration <= 660, start_time >= 690))  # Avoid 660-690
s.add(Or(start_time + duration <= 750, start_time >= 780))  # Avoid 750-780

# Theresa's busy periods: 12:00-12:30 (720-750), 15:00-15:30 (900-930)
s.add(Or(start_time + duration <= 720, start_time >= 750))  # Avoid 720-750
s.add(Or(start_time + duration <= 900, start_time >= 930))  # Avoid 900-930

# Shirley's busy periods: 9:30-10:30 (570-630), 11:00-12:00 (660-720), 
# 13:00-14:00 (780-840), 15:30-16:30 (930-990)
s.add(Or(start_time + duration <= 570, start_time >= 630))  # Avoid 570-630
s.add(Or(start_time + duration <= 660, start_time >= 720))  # Avoid 660-720
s.add(Or(start_time + duration <= 780, start_time >= 840))  # Avoid 780-840
s.add(Or(start_time + duration <= 930, start_time >= 990))  # Avoid 930-990

if s.check() == sat:
    m = s.model()
    start = m[start_time].as_long()
    hours = start // 60
    minutes = start % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")