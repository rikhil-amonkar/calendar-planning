from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (one hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 maps to 0 and 17:00 maps to 480 (in minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals are represented as (start, end) in minutes after 9:00.

# Madison is free the entire day, so no busy intervals.

# Judith's busy intervals:
#   10:00 to 10:30 -> [60, 90)
#   11:00 to 12:00 -> [120, 180)
#   12:30 to 13:00 -> [210, 240)
judith_busy = [(60, 90), (120, 180), (210, 240)]

# Roger's busy intervals:
#   9:00 to 9:30   -> [0, 30)
#   10:30 to 11:00 -> [90, 120)
#   12:00 to 12:30 -> [180, 210)
#   13:00 to 13:30 -> [240, 270)
#   14:00 to 16:00 -> [300, 420)
roger_busy = [(0, 30), (90, 120), (180, 210), (240, 270), (300, 420)]

# Create an Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# The meeting must occur within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function to add constraints to avoid overlapping a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting must either end before the busy interval starts,
    # or start after the busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Enforce non-overlap conditions for Judith's busy times.
for interval in judith_busy:
    optimizer.add(no_overlap(S, interval))

# Enforce non-overlap conditions for Roger's busy times.
for interval in roger_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, optimize for the earliest meeting time.
optimizer.minimize(S)

if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 to HH:MM format.
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