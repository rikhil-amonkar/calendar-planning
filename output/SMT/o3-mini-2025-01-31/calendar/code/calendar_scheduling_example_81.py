from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (one hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 is represented as 0 minutes after 9:00, 17:00 as 480 minutes after 9:00
work_start = 0
work_end = 480

# Time conversion:
# 9:00   -> 0
# 9:30   -> 30
# 10:00  -> 60
# 10:30  -> 90
# 11:00  -> 120
# 11:30  -> 150
# 12:00  -> 180
# 13:00  -> 240
# 14:00  -> 300
# 14:30  -> 330
# 15:00  -> 360
# 15:30  -> 390
# 16:00  -> 420
# 16:30  -> 450
# 17:00  -> 480

# Jeremy's busy interval:
# 14:30 to 15:30 -> [330, 390)
jeremy_busy = [(330, 390)]

# Lawrence's busy intervals:
# 15:30 to 16:00 -> [390, 420)
# 16:30 to 17:00 -> [450, 480)
lawrence_busy = [(390, 420), (450, 480)]

# Helen's busy intervals:
# 9:30 to 10:00   -> [30, 60)
# 10:30 to 11:00  -> [90, 120)
# 11:30 to 12:00  -> [150, 180)
# 13:00 to 14:00  -> [240, 300)
# 15:00 to 15:30  -> [360, 390)
# 16:00 to 17:00  -> [420, 480)
helen_busy = [(30, 60), (90, 120), (150, 180), (240, 300), (360, 390), (420, 480)]

# Create an Optimize instance for scheduling.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00)
S = Int('S')

# Ensure the meeting is within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function to ensure that the meeting [S, S+meeting_duration) does not overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Either the meeting ends on or before the busy interval starts, 
    # or starts on or after the busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Jeremy.
for interval in jeremy_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Lawrence.
for interval in lawrence_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Helen.
for interval in helen_busy:
    optimizer.add(no_overlap(S, interval))

# Minimize the meeting start time to select the earliest valid slot.
optimizer.minimize(S)

# Check if a valid meeting time is found.
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