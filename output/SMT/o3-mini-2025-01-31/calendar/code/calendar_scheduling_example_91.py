from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (1 hour = 60 minutes)
meeting_duration = 60

# Define work hours: from 9:00 (0 minutes) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Helper function to convert a time string like "9:00" to minutes after 9:00.
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return (hours - 9) * 60 + minutes

# Busy intervals for each participant (in minutes after 9:00)
# Danielle's busy intervals:
#   9:00-10:00   -> [0, 60)
#   10:30-11:00  -> [90, 120)
#   14:30-15:00  -> [330, 360)
#   15:30-16:00  -> [390, 420)
#   16:30-17:00  -> [450, 480)
danielle_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Bruce's busy intervals:
#   11:00-11:30  -> [120, 150)
#   12:30-13:00  -> [210, 240)
#   14:00-14:30  -> [300, 330)
#   15:30-16:00  -> [390, 420)
bruce_busy = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Eric's busy intervals:
#   9:00-9:30    -> [0, 30)
#   10:00-11:00  -> [60, 120)
#   11:30-13:00  -> [150, 240)
#   14:30-15:30  -> [330, 390)
eric_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:30"))
]

# Create an Optimize instance from Z3.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# The meeting must be scheduled within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# The meeting must not overlap with any participant's busy time.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting [s, s + meeting_duration) does not overlap with busy interval [busy_start, busy_end)
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Danielle's busy times.
for interval in danielle_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Bruce's busy times.
for interval in bruce_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Eric's busy times.
for interval in eric_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, minimize S to choose the earliest feasible meeting time.
optimizer.minimize(S)

# Check if a solution exists.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Utility function to convert minutes-after-9:00 back to HH:MM format.
    def minutes_to_time(minutes_after_nine):
        total_minutes = 9 * 60 + minutes_after_nine
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    print("A possible meeting time is:")
    print("Start:", minutes_to_time(meeting_start))
    print("End:  ", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")