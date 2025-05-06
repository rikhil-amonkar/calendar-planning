from z3 import *

# Helper functions to convert between time strings and minutes.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting configuration.
meeting_duration = 30  # half an hour meeting
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")  # 1020 minutes

# Roger's preference: avoid meetings on Monday before 12:30.
roger_preference = time_to_minutes("12:30")  # 750 minutes

# Busy intervals for each participant on Monday (in minutes).

# Daniel: free all day.

# Kathleen is busy during 14:30 to 15:30.
kathleen_busy = [
    (time_to_minutes("14:30"), time_to_minutes("15:30"))
]

# Carolyn is busy during 12:00 to 12:30 and 13:00 to 13:30.
carolyn_busy = [
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30"))
]

# Roger: free all day (except his preference; we'll enforce that separately).

# Cheryl is busy during 9:00 to 9:30, 10:00 to 11:30, 12:30 to 13:30, and 14:00 to 17:00.
cheryl_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("17:00"))
]

# Virginia is busy during 9:30 to 11:30, 12:00 to 12:30, 13:00 to 13:30, 
# 14:30 to 15:30, and 16:00 to 17:00.
virginia_busy = [
    (time_to_minutes("9:30"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Angela is busy during 9:30 to 10:00, 10:30 to 11:30, 12:00 to 12:30,
# 13:00 to 13:30, and 14:00 to 16:30.
angela_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("16:30"))
]

# Combine all busy intervals (except Daniel and Roger's already preference) 
# into one list.
all_busy_intervals = (kathleen_busy + carolyn_busy + cheryl_busy +
                      virginia_busy + angela_busy)

# Create a Z3 solver instance.
s = Solver()

# Define the meeting start time (in minutes from midnight).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: Meeting must be scheduled within work hours.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# Constraint 2: Roger's preference: do not schedule the meeting before 12:30.
s.add(meeting_start >= roger_preference)

# Constraint 3: The meeting must not overlap any busy interval of any participant.
for busy_start, busy_end in all_busy_intervals:
    # For each busy interval, the meeting must finish before it starts, or start after it ends.
    s.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Find a solution.
if s.check() == sat:
    model = s.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")