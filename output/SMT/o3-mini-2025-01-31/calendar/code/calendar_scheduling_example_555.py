from z3 import Optimize, Int, Or, sat

# Helper functions for time conversion.
def time_to_minutes(t):
    # Converts "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes since midnight to a "HH:MM" string.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")    # 9:00 AM
work_end   = time_to_minutes("17:00")    # 5:00 PM

# Evelyn's personal constraint: do not meet on Monday after 13:00.
# This means the meeting must finish by 13:00.
evelyn_latest_end = time_to_minutes("13:00")

# Busy intervals on Monday.
# Evelyn has no meetings.
# Randy is busy: 9:00-10:30, 11:00-15:30, and 16:00-17:00.
randy_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Create a Z3 optimizer.
opt = Optimize()

# Decision variable: meeting_start is the meeting's start time (in minutes from midnight on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to be scheduled within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Enforce Evelyn's constraint that the meeting must end by 13:00.
opt.add(meeting_end <= evelyn_latest_end)

# Function to add busy interval constraints.
def add_busy_constraints(busy_times):
    for busy_start, busy_end in busy_times:
        # The meeting must finish before a busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add busy constraints for Randy.
add_busy_constraints(randy_busy)

# Objective: schedule the meeting at the earliest available time.
opt.minimize(meeting_start)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    chosen_start = model[meeting_start].as_long()
    chosen_end = chosen_start + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(chosen_start))
    print("End:  ", minutes_to_time(chosen_end))
else:
    print("No valid meeting time could be found.")