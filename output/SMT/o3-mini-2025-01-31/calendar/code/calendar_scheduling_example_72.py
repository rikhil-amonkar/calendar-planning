from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (one hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 mapped to 0 and 17:00 mapped to 480 (minutes after 9:00)
work_start = 0
work_end = 480

# For our time conversion (minutes after 9:00):
# 9:00   -> 0
# 9:30   -> 30
# 10:00  -> 60
# 11:30  -> 150
# 12:00  -> 180
# 13:00  -> 240
# 13:30  -> 270
# 14:30  -> 330
# 15:00  -> 360
# 15:30  -> 390
# 16:30  -> 450
# 17:00  -> 480

# Mason is free the entire day, so no busy intervals.

# Amy's busy intervals on Monday:
# 9:30 to 11:30   -> [30, 150)
# 13:00 to 13:30  -> [240, 270)
# 16:30 to 17:00  -> [450, 480)
amy_busy = [(30, 150), (240, 270), (450, 480)]

# Christopher's busy intervals on Monday:
# 9:00 to 10:00   -> [0, 60)
# 12:00 to 13:30  -> [180, 270)
# 14:30 to 15:00  -> [330, 360)
# 15:30 to 16:30  -> [390, 450)
christopher_busy = [(0, 60), (180, 270), (330, 360), (390, 450)]

# Create an optimizer instance.
optimizer = Optimize()

# Define the meeting start time S (minutes after 9:00)
S = Int('S')

# The meeting must be scheduled within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function to ensure the meeting does not overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting [s, s+meeting_duration) must be either entirely before the busy interval or entirely after it.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add busy constraints for Amy.
for interval in amy_busy:
    optimizer.add(no_overlap(S, interval))

# Add busy constraints for Christopher.
for interval in christopher_busy:
    optimizer.add(no_overlap(S, interval))

# We want the earliest feasible meeting time, so minimize S.
optimizer.minimize(S)

# Check for a solution.
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