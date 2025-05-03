from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Work hours: from 9:00 (0 minutes after 9:00) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Time conversion reference (minutes after 9:00):
# 9:00    -> 0
# 9:30    -> 30
# 10:00   -> 60
# 10:30   -> 90
# 11:00   -> 120
# 11:30   -> 150
# 12:00   -> 180
# 12:30   -> 210
# 13:00   -> 240
# 13:30   -> 270
# 15:30   -> 390
# 16:00   -> 420
# 16:30   -> 450
# 17:00   -> 480

# Busy intervals are represented as [start, end) in minutes after 9:00.

# Adam is busy on Monday during:
#   9:30 to 10:00   -> [30, 60)
#   10:30 to 11:00  -> [90, 120)
#   11:30 to 12:00  -> [150, 180)
#   16:30 to 17:00  -> [450, 480)
adam_busy = [(30, 60), (90, 120), (150, 180), (450, 480)]

# Willie is busy on Monday during:
#   9:00 to 9:30   -> [0, 30)
#   15:30 to 16:00 -> [390, 420)
willie_busy = [(0, 30), (390, 420)]

# Gloria is busy on Monday during:
#   9:30 to 12:30  -> [30, 210)
#   13:00 to 13:30 -> [240, 270)
#   15:30 to 16:00 -> [390, 420)
gloria_busy = [(30, 210), (240, 270), (390, 420)]

# Gloria's preference: avoid meetings after 15:30.
# We interpret this as a preference to finish the meeting by 15:30.
# Since the meeting duration is 30 minutes, we add a constraint that the meeting must finish by 15:30.
# That is, meeting start S must satisfy: S + meeting_duration <= 390.
# (This is a soft constraint in nature, but here we add it as a hard constraint since a solution exists.)
gloria_preference = (lambda S: S + meeting_duration <= 390)

# Create an Optimize instance from Z3.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00)
S = Int('S')

# The meeting must lie within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Add Gloria's preference (meeting ends by 15:30).
optimizer.add(gloria_preference(S))

# Helper function: ensures that the meeting interval [S, S+duration) does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Meeting ends on or before busy_start or starts on or after busy_end.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for each participant's busy intervals.
for interval in adam_busy:
    optimizer.add(no_overlap(S, interval))

for interval in willie_busy:
    optimizer.add(no_overlap(S, interval))

for interval in gloria_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, minimize S to get the earliest available meeting time.
optimizer.minimize(S)

# Check for a valid meeting time.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Utility function to convert minutes-after-9:00 to a HH:MM string.
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