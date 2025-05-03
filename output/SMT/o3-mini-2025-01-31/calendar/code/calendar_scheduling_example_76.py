from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (one hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 is represented as 0 and 17:00 as 480 (minutes after 9:00)
work_start = 0
work_end = 480

# Time mapping (minutes after 9:00):
# 9:00    -> 0
# 9:30    -> 30
# 10:00   -> 60
# 10:30   -> 90
# 11:00   -> 120
# 11:30   -> 150
# 12:30   -> 210
# 13:00   -> 240
# 14:00   -> 300
# 14:30   -> 330
# 15:30   -> 390
# 16:00   -> 420
# 16:30   -> 450
# 17:00   -> 480

# Joyce has no meetings, so no busy intervals.

# Beverly's busy intervals on Monday:
# 9:30 to 10:00   -> [30, 60)
# 11:00 to 11:30  -> [120, 150)
# 12:30 to 13:00  -> [210, 240)
# 14:00 to 14:30  -> [300, 330)
# 15:30 to 16:00  -> [390, 420)
# 16:30 to 17:00  -> [450, 480)
beverly_busy = [(30, 60), (120, 150), (210, 240), (300, 330), (390, 420), (450, 480)]

# Peter's busy intervals on Monday:
# 9:30 to 10:30   -> [30, 90)
# 11:30 to 13:00  -> [150, 240)
# 14:30 to 15:30  -> [330, 390)
# 16:30 to 17:00  -> [450, 480)
peter_busy = [(30, 90), (150, 240), (330, 390), (450, 480)]

# Create an Optimize instance.
optimizer = Optimize()

# Define meeting start time S (in minutes after 9:00).
S = Int('S')

# Ensure the meeting is scheduled within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Define helper function to ensure no overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Meeting [s, s+meeting_duration) does not overlap busy [busy_start, busy_end) if:
    # either the meeting ends on or before busy interval starts, or starts on or after busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Beverly's busy intervals.
for interval in beverly_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Peter's busy intervals.
for interval in peter_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, you can minimize S to find the earliest meeting time.
optimizer.minimize(S)

if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # helper function to convert minutes-after-9:00 to HH:MM format
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