from z3 import *

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30 minutes meeting
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")  # 1020 minutes

# Wayne's preference: avoid meetings on Monday before 14:00.
wayne_preference = time_to_minutes("14:00")  # 840 minutes

# Busy intervals for each participant (in minutes):

# Wayne: free all day (only preference applies).

# Melissa's busy intervals.
melissa_busy = [
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("12:30"), time_to_minutes("14:00")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Catherine is free all day.

# Gregory's busy intervals.
gregory_busy = [
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Victoria's busy intervals.
victoria_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:30"))
]

# Thomas's busy intervals.
thomas_busy = [
    (time_to_minutes("10:00"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:30"), time_to_minutes("16:00"))
]

# Jennifer's busy intervals.
jennifer_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Create a Z3 solver instance.
s = Solver()

# Define the meeting start time (in minutes).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: The meeting must be scheduled within work hours.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# Constraint 2: Apply Wayne's preference: meeting must start at or after 14:00.
s.add(meeting_start >= wayne_preference)

# Helper function to add busy interval constraints.
def add_busy_constraints(busy_intervals):
    for start_busy, end_busy in busy_intervals:
        # The meeting must either finish before a busy interval starts, or start after it ends.
        s.add(Or(meeting_end <= start_busy, meeting_start >= end_busy))

# Add constraints for each participant's busy intervals.
add_busy_constraints(melissa_busy)
add_busy_constraints(gregory_busy)
add_busy_constraints(victoria_busy)
add_busy_constraints(thomas_busy)
add_busy_constraints(jennifer_busy)
# (Wayne and Catherine are free, aside from Wayne's scheduling preference.)

# Check if a valid meeting time exists.
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_time))
    print("End:  ", minutes_to_time(end_time))
else:
    print("No valid meeting time could be found.")