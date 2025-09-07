from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

s = Solver()

start = Int('start')

s.add(start >= 540)  # 9:00 AM in minutes since midnight
s.add(start <= 990)  # 4:30 PM (start + 30 <= 5:00 PM)

# Nicole's existing meetings: 9:00-10:00 and 10:30-4:30
# Ensure no overlap with these intervals
s.add(Or(start + 30 <= 540, start >= 600))  # No overlap with 9:00-10:00
s.add(Or(start + 30 <= 630, start >= 990))  # No overlap with 10:30-4:30

# Preference: Not before 4:00 PM (960 minutes)
s.add(start >= 960)

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_long()
    end_time = start_time + 30
    day = "Monday"
    print(f"{{{minutes_to_time(start_time)}:{minutes_to_time(end_time)}}} {day}")
else:
    print("No solution")