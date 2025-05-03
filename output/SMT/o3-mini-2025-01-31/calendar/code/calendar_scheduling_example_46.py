from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Define working hours in minutes after 9:00. 9:00 is 0 minutes and 17:00 is 480 minutes.
work_start = 0
work_end = 480

# Arthur's busy intervals (minutes after 9:00):
# 9:30 to 10:00  -> [30, 60)
# 14:00 to 14:30 -> [300, 330)
arthur_busy = [(30, 60), (300, 330)]

# Theresa's busy intervals:
# 9:00 to 9:30   -> [0, 30)
# 12:00 to 13:00 -> [180, 240)
# 15:00 to 16:30 -> [360, 450)
theresa_busy = [(0, 30), (180, 240), (360, 450)]

# Carl's busy intervals:
# 9:00 to 11:30  -> [0, 150)
# 12:00 to 14:00 -> [180, 300)
# 14:30 to 17:00 -> [330, 480)
carl_busy = [(0, 150), (180, 300), (330, 480)]

# Create the optimizer instance.
optimizer = Optimize()

# Define the meeting start time variable (in minutes after 9:00).
S = Int('S')

# The meeting must start and finish within the working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Utility function to enforce that the meeting [S, S+duration) does not overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # No overlap if the meeting ends on or before busy_start or starts on or after busy_end.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints to avoid overlapping Arthur's busy times.
for interval in arthur_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Theresa's busy times.
for interval in theresa_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Carl's busy times.
for interval in carl_busy:
    optimizer.add(no_overlap(S, interval))

# The group prefers to meet at the earliest available time.
optimizer.minimize(S)

# Check and print the meeting time if a solution is found.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration
    
    # Helper function to convert minutes after 9:00 into HH:MM (24-hour format)
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