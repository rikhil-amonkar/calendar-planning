from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Work hours: 9:00 is represented as 0 and 17:00 as 480 (minutes after 9:00)
work_start = 0
work_end = 480

# Time mapping (minutes after 9:00):
# 9:00   -> 0
# 9:30   -> 30
# 10:00  -> 60
# 10:30  -> 90
# 11:00  -> 120
# 11:30  -> 150
# 12:00  -> 180
# 12:30  -> 210
# 13:00  -> 240
# 13:30  -> 270
# 14:00  -> 300
# 14:30  -> 330
# 15:00  -> 360
# 15:30  -> 390
# 16:00  -> 420
# 16:30  -> 450
# 17:00  -> 480

# Donald's busy intervals on Monday:
# 10:00 to 10:30 -> [60, 90)
# 11:00 to 11:30 -> [120, 150)
# 12:00 to 12:30 -> [180, 210)
# 13:00 to 13:30 -> [240, 270)
# 15:30 to 16:30 -> [390, 450)
donald_busy = [(60, 90), (120, 150), (180, 210), (240, 270), (390, 450)]

# Joyce's busy intervals on Monday:
# 11:00 to 13:00 -> [120, 180)
# 14:30 to 15:00 -> [330, 360)
# 16:00 to 16:30 -> [420, 450)
joyce_busy = [(120, 180), (330, 360), (420, 450)]

# Abigail's busy intervals on Monday:
# 9:30 to 10:00  -> [30, 60)
# 11:30 to 12:00 -> [150, 180)
# 13:00 to 14:00 -> [240, 300)
# 15:00 to 17:00 -> [360, 480)
abigail_busy = [(30, 60), (150, 180), (240, 300), (360, 480)]

# Create an Optimize instance.
optimizer = Optimize()

# Define meeting start time S (in minutes after 9:00).
S = Int('S')

# Ensure the meeting is scheduled within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Donald does not want to meet after 12:00. Interpret this as the meeting must finish by 12:00.
optimizer.add(S + meeting_duration <= 180)  # 12:00 is 180 minutes after 9:00

# Define helper function to ensure that the meeting [S, S+meeting_duration)
# does not overlap with a busy interval [busy_start, busy_end)
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting doesn't overlap if it ends on/before the busy interval starts or starts on/after busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for Donald.
for interval in donald_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Joyce.
for interval in joyce_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Abigail.
for interval in abigail_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, minimize S to find the earliest possible meeting time.
optimizer.minimize(S)

if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes-after-9:00 to HH:MM format.
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