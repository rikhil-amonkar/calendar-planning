from z3 import Optimize, Int, Or

# Helper functions to convert between time strings and minutes.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # 1 hour meeting.
work_start = time_to_minutes("9:00")   # 540 minutes.
work_end   = time_to_minutes("17:00")  # 1020 minutes.

# Denise's preference: do not meet on Monday after 12:30.
# We'll enforce that the entire meeting must finish by 12:30.
denise_latest_end = time_to_minutes("12:30")  # 750 minutes.

# Busy intervals for Monday (in minutes).
# Format: (busy_start, busy_end).
ryan_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00"))
]

denise_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:30")),
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("14:30"), time_to_minutes("16:30"))  # This will be irrelevant due to Denise's after-12:30 preference.
]

# Create an Optimize solver so we can choose the earliest available time.
opt = Optimize()

# Since the meeting is on Monday, we work with a single day.
# Define the meeting start time (in minutes).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: The meeting must be within the work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Constraint 2: Enforce Denise's preference: the meeting must finish by 12:30.
opt.add(meeting_end <= denise_latest_end)

# Constraint 3: The meeting must not overlap any participant's busy intervals.
# For an interval [a, b] that is busy, we require that either:
#    meeting_end <= a   or   meeting_start >= b
def add_busy_constraints(busy_intervals):
    for start_busy, end_busy in busy_intervals:
        opt.add(Or(meeting_end <= start_busy, meeting_start >= end_busy))

add_busy_constraints(ryan_busy)
add_busy_constraints(denise_busy)

# Objective: Choose the earliest available meeting start time.
opt.minimize(meeting_start)

# Check for a valid meeting time.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")