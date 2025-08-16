from z3 import *

# Create a Z3 solver instance
s = Solver()

# Variables:
# day: 0 for Monday, 1 for Tuesday
day = Int('day')
# meeting start time in minutes after 9:00 (so 0 corresponds to 09:00).
start = Int('start')
duration = 30  # meeting duration in minutes

# Domain constraints:
s.add(Or(day == 0, day == 1))
# Meeting must start and finish within work hours: 09:00 to 17:00.
s.add(start >= 0, start + duration <= 8 * 60)  # 8 hours = 480 minutes total, start +30 <= 480

# Margaret's constraints:
# 1. Margaret does not want to meet on Monday.
s.add(day != 0)
# 2. On Tuesday, she does not want meetings before 14:30.
# 14:30 is 5.5 hours after 9:00 → 5.5 * 60 = 330 minutes.
s.add(Implies(day == 1, start >= 330))

# Alexis's constraints (for Tuesday):
# On Tuesday, Alexis has a meeting from 14:00 to 16:30.
# Convert 14:00 and 16:30 to minutes after 9:00:
#   14:00 → (14-9)*60 = 300 minutes, 16:30 → (16.5-9)*60 = 450 minutes.
# To avoid overlapping with a block [300, 450],
# the meeting [start, start+30] must either finish by 14:00 or start after 16:30.
# Given Margaret’s Tuesday constraint (start >=330), only the "start after 16:30" option is viable.
s.add(Implies(day == 1, Or(start + duration <= 300, start >= 450)))

# (Other busy blocks for Alexis on Tuesday [09:00-09:30] and [10:00-10:30],
#  and for Margaret on Tuesday [12:00-12:30] are earlier than 14:30, so we need not worry about them.)

# Solve the constraints
if s.check() == sat:
    m = s.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    end_val = start_val + duration

    # Convert day integer to day name
    day_str = "Monday" if day_val == 0 else "Tuesday"
    
    # Function to convert minutes after 9:00 to HH:MM (24-hour format)
    def to_time(minutes_after_nine):
        total_minutes = 9 * 60 + minutes_after_nine
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    start_time_str = to_time(start_val)
    end_time_str = to_time(end_val)
    
    print("SOLUTION:")
    print("Day:", day_str)
    print("Start Time:", start_time_str)
    print("End Time:", end_time_str)
else:
    print("No solution found.")