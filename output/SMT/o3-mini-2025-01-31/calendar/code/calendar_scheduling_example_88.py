from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (1 hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 (0 minutes after 9:00) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Time conversion reference (minutes after 9:00):
# 9:00   -> 0
# 9:30   -> 30
# 10:30  -> 90
# 11:30  -> 150
# 12:00  -> 180
# 12:30  -> 210
# 13:00  -> 240
# 13:30  -> 270
# 14:00  -> 300
# 14:30  -> 330
# 17:00  -> 480

# Dennis has no meetings, hence no busy intervals.

# Joseph's busy intervals:
# 9:00 to 9:30   -> [0, 30)
# 12:30 to 13:00 -> [210, 240)
joseph_busy = [(0, 30), (210, 240)]

# Isabella's busy intervals:
# 9:00 to 10:30  -> [0, 90)
# 11:30 to 12:00 -> [150, 180)
# 13:30 to 14:00 -> [270, 300)
# 14:30 to 17:00 -> [330, 480)
isabella_busy = [(0, 90), (150, 180), (270, 300), (330, 480)]

# Create a Z3 Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00)
S = Int('S')

# Ensure the meeting lies within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function to ensure meeting interval [S, S+duration)
# does not overlap with a given busy interval [busy_start, busy_end)
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Either the meeting ends on or before the busy interval starts,
    # or it starts on or after the busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Joseph's constraints
for interval in joseph_busy:
    optimizer.add(no_overlap(S, interval))

# Isabella's constraints
for interval in isabella_busy:
    optimizer.add(no_overlap(S, interval))

# Optional: minimize S to get the earliest available meeting time.
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