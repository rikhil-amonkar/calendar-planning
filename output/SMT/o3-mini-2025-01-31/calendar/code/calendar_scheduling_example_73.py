from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Work hours: 9:00 is mapped to 0 and 17:00 is mapped to 480 (minutes after 9:00)
work_start = 0
work_end = 480

# For our reference (minutes after 9:00):
# 9:00   -> 0
# 9:30   -> 30
# 10:00  -> 60
# 10:30  -> 90
# 11:00  -> 120
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

# Bradley's busy intervals on Monday:
# 9:30 to 10:00  -> [30, 60)
# 13:00 to 13:30 -> [240, 270)
# 14:30 to 15:00 -> [330, 360)
# 16:30 to 17:00 -> [450, 480)
bradley_busy = [(30, 60), (240, 270), (330, 360), (450, 480)]

# Andrew's busy intervals on Monday:
# 9:00 to 9:30   -> [0, 30)
# 12:30 to 13:30 -> [210, 270)
# 14:00 to 14:30 -> [300, 330)
# 15:00 to 16:00 -> [360, 420)
andrew_busy = [(0, 30), (210, 270), (300, 330), (360, 420)]

# Melissa's busy intervals on Monday:
# 9:00 to 9:30   -> [0, 30)
# 10:00 to 10:30 -> [60, 90)
# 11:00 to 14:00 -> [120, 300)
# 15:00 to 15:30 -> [360, 390)
# 16:00 to 16:30 -> [420, 450)
melissa_busy = [(0, 30), (60, 90), (120, 300), (360, 390), (420, 450)]

# Create an Optimize instance for finding the earliest meeting start time.
optimizer = Optimize()

# Define the meeting start time S (minutes after 9:00)
S = Int('S')

# Enforce the meeting to be within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function to make sure the meeting [S, S+meeting_duration) doesn't overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Bradley's busy intervals.
for interval in bradley_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Andrew's busy intervals.
for interval in andrew_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Melissa's busy intervals.
for interval in melissa_busy:
    optimizer.add(no_overlap(S, interval))

# To find the earliest available time slot, minimize S.
optimizer.minimize(S)

# Check for a valid solution.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 to a HH:MM formatted string.
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