from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Work hours: 9:00 (0 minutes after 9:00) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Time conversion reference (minutes after 9:00):
# 9:00   -> 0
# 9:30   -> 30
# 10:00  -> 60
# 10:30  -> 90
# 11:30  -> 150
# 12:00  -> 180
# 13:00  -> 240
# 13:30  -> 270
# 14:30  -> 330
# 15:00  -> 360
# 15:30  -> 390
# 16:00  -> 420
# 16:30  -> 450
# 17:00  -> 480

# Brittany's busy intervals:
# 12:00 to 13:30 -> [180,270)
# 14:30 to 15:00 -> [330,360)
# 15:30 to 16:00 -> [390,420)
# 16:30 to 17:00 -> [450,480)
brittany_busy = [(180, 270), (330, 360), (390, 420), (450, 480)]

# Wayne's busy intervals:
# 9:30 to 10:00 -> [30,60)
# 13:00 to 15:00 -> [240,360)
# 16:30 to 17:00 -> [450,480)
wayne_busy = [(30, 60), (240, 360), (450, 480)]

# Charles's busy intervals:
# 9:00 to 9:30   -> [0, 30)
# 10:00 to 10:30 -> [60, 90)
# 11:30 to 13:30 -> [150,270)
# 14:30 to 16:30 -> [330,450)
charles_busy = [(0, 30), (60, 90), (150, 270), (330, 450)]

# Create a Z3 Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# Meeting must be within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function to ensure the meeting interval [S, S+meeting_duration)
# does not overlap with a given busy time interval [busy_start, busy_end)
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Brittany's busy intervals.
for interval in brittany_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Wayne's busy intervals.
for interval in wayne_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Charles's busy intervals.
for interval in charles_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, we choose to minimize S to get the earliest available meeting time.
optimizer.minimize(S)

# Check if a valid meeting time exists.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Utility function to convert minutes-after-9:00 to HH:MM format.
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