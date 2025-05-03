from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (one hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 mapped to 0 and 17:00 mapped to 480 (minutes after 9:00)
work_start = 0
work_end = 480

# Convert time to minutes after 9:00:
# 9:00  -> 0
# 10:00 -> 60
# 11:00 -> 120
# 11:30 -> 150
# 13:00 -> 240
# 13:30 -> 270
# 14:00 -> 300
# 15:00 -> 360
# 15:30 -> 390
# 16:00 -> 420
# 16:30 -> 450
# 17:00 -> 480

# Shirley's busy intervals (in minutes after 9:00):
#   11:00 to 11:30 -> [120, 150)
#   14:00 to 15:00 -> [300, 360)
#   16:00 to 16:30 -> [420, 450)
shirley_busy = [(120, 150), (300, 360), (420, 450)]

# Stephen's busy intervals:
#   13:00 to 13:30 -> [240, 270)
#   15:30 to 16:00 -> [390, 420)
stephen_busy = [(240, 270), (390, 420)]

# Paul's busy intervals:
#   9:00 to 10:00  -> [0, 60)
#   11:00 to 17:00 -> [120, 480)
paul_busy = [(0, 60), (120, 480)]

# Create an Optimize instance
optimizer = Optimize()

# Define the meeting start time S (minutes after 9:00)
S = Int('S')

# The meeting must be scheduled within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function to ensure the meeting does not overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Shirley's busy times.
for interval in shirley_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Stephen's busy times.
for interval in stephen_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Paul's busy times.
for interval in paul_busy:
    optimizer.add(no_overlap(S, interval))

# We want the earliest possible meeting time, so minimize S.
optimizer.minimize(S)

# Check for a solution.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Function to convert minutes (after 9:00) into HH:MM format.
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