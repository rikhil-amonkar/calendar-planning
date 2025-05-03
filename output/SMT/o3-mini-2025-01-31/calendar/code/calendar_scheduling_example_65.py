from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Work hours: 9:00 maps to 0 and 17:00 maps to 480 (in minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals for each participant are represented as (start, end) in minutes after 9:00.

# John's busy intervals:
#   12:30 to 13:00 -> [210, 240)
#   15:30 to 16:00 -> [390, 420)
john_busy = [(210, 240), (390, 420)]

# Andrea's busy intervals:
#   9:00 to 9:30 -> [0, 30)
#   11:00 to 12:30 -> [120, 210)
#   15:00 to 15:30 -> [360, 390)
#   16:00 to 16:30 -> [420, 450)
andre_busy = [(0, 30), (120, 210), (360, 390), (420, 450)]

# Additionally, Andrea cannot meet on Monday after 16:30.
# This means that the meeting must finish by 16:30 (i.e. S + meeting_duration <= 450)

# Lisa's busy intervals:
#   9:00 to 10:00 -> [0, 60)
#   10:30 to 11:00 -> [90, 120)
#   12:00 to 12:30 -> [180, 210)
#   14:00 to 15:30 -> [300, 390)
#   16:00 to 16:30 -> [420, 450)
lisa_busy = [(0, 60), (90, 120), (180, 210), (300, 390), (420, 450)]

# Create an Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# The meeting must occur within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Enforce Andrea's constraint that the meeting must finish by 16:30.
optimizer.add(S + meeting_duration <= 450)

# Helper function that returns a constraint ensuring that a meeting starting at time s
# does not overlap with a given busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting must either end before the busy interval starts,
    # or start after the busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for John's busy intervals.
for interval in john_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Andrea's busy intervals.
for interval in andre_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Lisa's busy intervals.
for interval in lisa_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, choose the earliest valid meeting time by minimizing S.
optimizer.minimize(S)

if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 to HH:MM.
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