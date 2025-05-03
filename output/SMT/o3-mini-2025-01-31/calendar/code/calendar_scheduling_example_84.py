from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (one hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 corresponds to 0 minutes and 17:00 corresponds to 480 minutes after 9:00.
work_start = 0
work_end = 480

# Time conversion reference (minutes after 9:00):
# 9:00   -> 0
# 9:30   -> 30
# 10:00  -> 60
# 10:30  -> 90
# 11:00  -> 120
# 11:30  -> 150
# 12:30  -> 210
# 13:00  -> 240
# 13:30  -> 270
# 14:00  -> 300
# 15:00  -> 360
# 16:00  -> 420
# 17:00  -> 480

# Kevin's busy intervals:
# 9:30 to 10:00 -> [30, 60)
# 10:30 to 11:00 -> [90, 120)
# 15:00 to 16:00 -> [360, 420)
kevin_busy = [(30, 60), (90, 120), (360, 420)]

# Ryan's busy intervals:
# 10:30 to 11:30 -> [90, 150)
# 12:30 to 13:00 -> [210, 240)
# 13:30 to 14:00 -> [270, 300)
ryan_busy = [(90, 150), (210, 240), (270, 300)]

# Eugene's busy intervals:
# 9:00 to 9:30   -> [0, 30)
# 10:00 to 11:00 -> [60, 120)
# 12:30 to 17:00 -> [210, 480)
eugene_busy = [(0, 30), (60, 120), (210, 480)]

# Create an Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# Add constraints for meeting to be within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Define a helper function to ensure the meeting does not overlap a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting [s, s+meeting_duration) does not overlap the busy interval [busy_start, busy_end)
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Kevin's busy intervals.
for interval in kevin_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Ryan's busy intervals.
for interval in ryan_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Eugene's busy intervals.
for interval in eugene_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, minimize S to choose the earliest valid slot.
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