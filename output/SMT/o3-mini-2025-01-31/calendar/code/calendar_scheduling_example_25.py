from z3 import *

# Helper function: convert a "HH:MM" time string to minutes from midnight.
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

# Helper function: convert minutes from midnight to "HH:MM" time string.
def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # one hour meeting.
work_start = time_to_minutes("9:00")    # 9:00 -> 540 minutes.
work_end   = time_to_minutes("17:00")   # 17:00 -> 1020 minutes.

# Additional constraint for Pamela: she does not want to meet after 14:30.
# We interpret this as the meeting must end by 14:30.
latest_end_for_pamela = time_to_minutes("14:30")  # 14:30 -> 870 minutes.

# Anthony's busy intervals on Monday.
anthony_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Pamela's busy intervals on Monday.
pamela_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Zachary's busy intervals on Monday.
zachary_busy = [
    (time_to_minutes("9:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Create a Z3 solver instance.
s = Solver()

# Declare the meeting start time in minutes.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: The meeting must be within work hours.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# Constraint 2: Pamela does not want meetings after 14:30,
# so the meeting must end by 14:30.
s.add(meeting_end <= latest_end_for_pamela)

# Constraint 3: The meeting must not overlap any participant's busy intervals.
# For each busy interval, apply: meeting_end <= busy_start OR meeting_start >= busy_end.

# For Anthony's intervals.
for busy_start, busy_end in anthony_busy:
    s.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# For Pamela's intervals.
for busy_start, busy_end in pamela_busy:
    s.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# For Zachary's intervals.
for busy_start, busy_end in zachary_busy:
    s.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Check for a valid meeting time.
if s.check() == sat:
    model = s.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")