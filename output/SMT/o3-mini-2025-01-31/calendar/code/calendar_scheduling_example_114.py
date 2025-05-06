from z3 import Optimize, Int, Or, sat

# Helper functions for time conversions.
def time_to_minutes(time_str):
    # Converts a time string "HH:MM" into minutes since midnight.
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def minutes_to_time(minutes):
    # Converts minutes since midnight back into a "HH:MM" string.
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # 1 hour meeting.
work_start = time_to_minutes("9:00")    # 540 minutes.
work_end   = time_to_minutes("17:00")   # 1020 minutes.

# Busy intervals for each participant on Monday (in minutes).

# Stephanie's busy intervals: 10:00-10:30, 16:00-16:30.
stephanie_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Cheryl's busy intervals: 10:00-10:30, 11:30-12:00, 13:30-14:00, 16:30-17:00.
cheryl_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Bradley's busy intervals: 9:30-10:00, 10:30-11:30, 13:30-14:00, 14:30-15:00, 15:30-17:00.
bradley_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Steven's busy intervals: 9:00-12:00, 13:00-13:30, 14:30-17:00.
steven_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("17:00"))
]

# Create the Z3 optimizer.
opt = Optimize()

# Decision variable: meeting start time (in minutes from midnight on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to occur within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add non-overlap constraints for a given set of busy intervals.
def add_busy_constraints(busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must either end before a busy interval starts
        # or start after the busy interval ends.
        opt.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add constraints for all participants.
add_busy_constraints(stephanie_busy)
add_busy_constraints(cheryl_busy)
add_busy_constraints(bradley_busy)
add_busy_constraints(steven_busy)

# Objective: find the earliest available meeting time.
opt.minimize(meeting_start)

# Check if there is a valid meeting time.
if opt.check() == sat:
    model = opt.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_time))
    print("End:  ", minutes_to_time(end_time))
else:
    print("No valid meeting time could be found.")