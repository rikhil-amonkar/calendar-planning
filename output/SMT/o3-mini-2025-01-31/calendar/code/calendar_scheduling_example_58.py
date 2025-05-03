from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (1 hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 equals 0 minutes; 17:00 equals 480 minutes (i.e., 8 hours)
work_start = 0
work_end = 480

# Convert busy intervals into minutes past 9:00.
# Joan's busy intervals:
#   11:00 to 11:30 -> [120, 150)
#   12:30 to 13:00 -> [210, 240)
joan_busy = [(120, 150), (210, 240)]

# Theresa's busy intervals:
#   12:00 to 12:30 -> [180, 210)
#   15:00 to 15:30 -> [360, 390)
theresa_busy = [(180, 210), (360, 390)]

# Shirley's busy intervals:
#   9:30 to 10:30   -> [30, 90)
#   11:00 to 12:00  -> [120, 180)
#   13:00 to 14:00  -> [240, 300)
#   15:30 to 16:30  -> [390, 450)
shirley_busy = [(30, 90), (120, 180), (240, 300), (390, 450)]

# Create an Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# The meeting must start within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function to enforce that the meeting does not overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting finishes before the busy interval begins, or starts after it ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Joan's schedule.
for interval in joan_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Theresa's schedule.
for interval in theresa_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Shirley's schedule.
for interval in shirley_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, we can require the earliest valid time by minimizing S.
optimizer.minimize(S)

# Check for a valid schedule.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Function to convert minutes after 9:00 to HH:MM.
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