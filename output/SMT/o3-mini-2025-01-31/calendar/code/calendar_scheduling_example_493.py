from z3 import *

# Helper functions to convert between time strings and minutes from midnight.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # half an hour meeting.
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")  # 1020 minutes

# Define busy intervals for each participant on Monday.
# Each interval is a tuple (start_time, end_time) in minutes.
# Participants with no meetings are simply skipped (no intervals added).

# Tyler: free the entire day -> no intervals.
# Kelly: no meetings -> no intervals.
# Stephanie's busy intervals.
stephanie_busy = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

# Hannah: free the entire day -> no intervals.
# Joe's busy intervals.
joe_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("17:00"))
]

# Diana's busy intervals.
diana_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Deborah's busy intervals.
deborah_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Combine all busy intervals in a list.
all_busy_intervals = stephanie_busy + joe_busy + diana_busy + deborah_busy

# Create a Z3 solver instance.
s = Solver()

# Declare an integer variable for the meeting start time (in minutes).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: Meeting must be within work hours.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# Constraint 2: The meeting must not overlap any busy interval.
for (busy_start, busy_end) in all_busy_intervals:
    # Either the meeting ends before a busy interval starts
    # or the meeting starts after a busy interval ends.
    s.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Check if a valid meeting time exists.
if s.check() == sat:
    model = s.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")