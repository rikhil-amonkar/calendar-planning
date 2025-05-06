from z3 import Optimize, Int, Or, sat

# Helper functions to convert between "HH:MM" strings and minutes since midnight.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration:
meeting_duration = 30  # A 30-minute meeting.
work_start = time_to_minutes("9:00")   # Work day starts at 9:00 AM (540 minutes).
work_end = time_to_minutes("17:00")    # Work day ends at 5:00 PM (1020 minutes).

# Busy intervals for each participant on Monday:

# Patrick is busy during:
#   9:00-9:30, 10:00-10:30, 13:30-14:00, 16:00-16:30.
patrick_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Kayla is busy during:
#   12:30-13:30, 15:00-15:30, 16:00-16:30.
kayla_busy = [
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Carl is busy during:
#   10:30-11:00, 12:00-12:30, 13:00-13:30, 14:30-17:00.
carl_busy = [
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("17:00"))
]

# Christian is busy during:
#   9:00-12:30, 13:00-14:00, 14:30-17:00.
christian_busy = [
    (time_to_minutes("9:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("17:00"))
]

# Create a Z3 optimizer.
opt = Optimize()

# Decision variable: meeting_start represents the start time (in minutes since midnight) on Monday.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting time to be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function that adds non-overlap constraints for a list of busy intervals.
def add_busy_constraints(busy_times):
    for start_busy, end_busy in busy_times:
        # The meeting must end on or before the busy interval starts,
        # or start on or after the busy interval ends.
        opt.add(Or(meeting_end <= start_busy, meeting_start >= end_busy))

# Add constraints for all participants.
add_busy_constraints(patrick_busy)
add_busy_constraints(kayla_busy)
add_busy_constraints(carl_busy)
add_busy_constraints(christian_busy)

# Objective: Use the earliest available meeting start time.
opt.minimize(meeting_start)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")