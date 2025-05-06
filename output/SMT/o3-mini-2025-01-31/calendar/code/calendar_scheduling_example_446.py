from z3 import *

# Helper functions to convert between time and minutes from midnight.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration: half-hour meeting between 9:00 and 17:00.
meeting_duration = 30
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")  # 1020 minutes

# Busy intervals on Monday for each participant (as (start, end) in minutes).

# Megan's busy intervals.
megan_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("12:00"), time_to_minutes("12:30"))
]

# Christine's busy intervals.
christine_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("14:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:30"))
]

# Gabriel is free the entire day, so no busy intervals.
gabriel_busy = []

# Sara's busy intervals.
sara_busy = [
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

# Bruce's busy intervals.
bruce_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:30"))
]

# Kathryn's busy intervals.
kathryn_busy = [
    (time_to_minutes("10:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Billy's busy intervals.
billy_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:30"))
]

# Combine all busy intervals.
all_busy_intervals = (megan_busy + christine_busy + gabriel_busy +
                      sara_busy + bruce_busy + kathryn_busy + billy_busy)

# Create a Z3 solver instance.
s = Solver()

# Define the meeting start time (in minutes).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: The meeting must be within work hours.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# Constraint 2: The meeting must not overlap any participant's busy intervals.
# For each interval: meeting must end before the busy interval starts or
# start after the busy interval ends.
for (busy_start, busy_end) in all_busy_intervals:
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