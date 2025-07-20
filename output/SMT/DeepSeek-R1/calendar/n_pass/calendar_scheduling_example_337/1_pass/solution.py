from z3 import *

def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Define the participants' busy intervals in minutes
busy_intervals = [
    # John's meetings
    [(time_to_minutes("11:30"), time_to_minutes("12:00")),
     (time_to_minutes("14:00"), time_to_minutes("14:30"))],
    # Megan's meetings
    [(time_to_minutes("12:00"), time_to_minutes("12:30")),
     (time_to_minutes("14:00"), time_to_minutes("15:00")),
     (time_to_minutes("15:30"), time_to_minutes("16:00"))],
    # Brandon has no meetings, so skip
    [],
    # Kimberly's meetings
    [(time_to_minutes("9:00"), time_to_minutes("9:30")),
     (time_to_minutes("10:00"), time_to_minutes("10:30")),
     (time_to_minutes("11:00"), time_to_minutes("14:30")),
     (time_to_minutes("15:00"), time_to_minutes("16:00")),
     (time_to_minutes("16:30"), time_to_minutes("17:00"))],
    # Sean's meetings
    [(time_to_minutes("10:00"), time_to_minutes("11:00")),
     (time_to_minutes("11:30"), time_to_minutes("14:00")),
     (time_to_minutes("15:00"), time_to_minutes("15:30"))],
    # Lori's meetings
    [(time_to_minutes("9:00"), time_to_minutes("9:30")),
     (time_to_minutes("10:30"), time_to_minutes("12:00")),
     (time_to_minutes("13:00"), time_to_minutes("14:30")),
     (time_to_minutes("16:00"), time_to_minutes("16:30"))]
]

# Initialize Z3 solver and variables
s = Solver()
start_time = Int('start_time')

# Constraints: meeting must be within 9:00 to 17:00 and last 30 minutes
s.add(start_time >= time_to_minutes("9:00"))
s.add(start_time <= time_to_minutes("16:30"))  # 16:30 + 30 min = 17:00

# Add constraints for each participant's busy intervals
for intervals in busy_intervals:
    for (busy_start, busy_end) in intervals:
        # The meeting does not overlap if it ends before busy_start or starts after busy_end
        s.add(Or(start_time + 30 <= busy_start, start_time >= busy_end))

# Check if a solution exists
if s.check() == sat:
    m = s.model()
    start_minutes = m[start_time].as_long()
    end_minutes = start_minutes + 30
    start_str = minutes_to_time(start_minutes)
    end_str = minutes_to_time(end_minutes)
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_str}")
    print(f"End Time: {end_str}")
else:
    print("No solution found")