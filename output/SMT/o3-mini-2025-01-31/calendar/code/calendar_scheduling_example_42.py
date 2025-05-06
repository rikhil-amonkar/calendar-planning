from z3 import *

# Helper functions for time conversion
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration
meeting_duration = 60  # 1 hour meeting
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")  # 1020 minutes

# Busy intervals for Monday (in minutes)

# Julie's busy intervals: [9:00, 9:30], [11:00, 11:30], [12:00, 12:30], [13:30, 14:00], [16:00, 17:00]
julie_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Sean's busy intervals: [9:00, 9:30], [13:00, 13:30], [15:00, 15:30], [16:00, 16:30]
sean_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Lori's busy intervals: [10:00, 10:30], [11:00, 13:00], [15:30, 17:00]
lori_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("13:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Create a Z3 Solver instance
s = Solver()

# Declare the meeting start time (in minutes from midnight)
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: The meeting must be within work hours.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function to add busy interval constraints.
def add_constraints(busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must end before a busy interval starts OR start after it ends.
        s.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Constraint 2: The meeting must not overlap the busy intervals of any participant.
add_constraints(julie_busy)
add_constraints(sean_busy)
add_constraints(lori_busy)

# Check for a valid meeting time.
if s.check() == sat:
    m = s.model()
    start_val = m[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")