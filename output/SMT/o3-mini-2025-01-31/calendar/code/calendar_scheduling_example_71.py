from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Work hours: 9:00 mapped to 0 and 17:00 mapped to 480 (minutes after 9:00)
work_start = 0
work_end = 480

# For our time conversion (minutes after 9:00):
# 9:00   -> 0
# 10:00  -> 60
# 10:30  -> 90
# 11:00  -> 120
# 11:30  -> 150
# 12:00  -> 180
# 12:30  -> 210
# 13:00  -> 240
# 14:00  -> 300
# 14:30  -> 330
# 16:30  -> 450
# 17:00  -> 480

# Nicole is free all day, so no busy intervals.

# John's busy intervals on Monday:
#   12:30 to 13:00 -> [210, 240)
#   16:30 to 17:00 -> [450, 480)
john_busy = [(210, 240), (450, 480)]

# John's preference: he would rather not meet after 12:00 (i.e. the meeting should end by 12:00).
# We add a constraint so that the meeting must finish by 12:00.
john_preference = (lambda S: S + meeting_duration <= 180)

# Ethan's busy intervals:
#   9:00 to 10:00   -> [0, 60)
#   11:30 to 14:00  -> [150, 300)
#   14:30 to 17:00  -> [330, 480)
ethan_busy = [(0, 60), (150, 300), (330, 480)]

# Create an optimizer instance.
optimizer = Optimize()

# Define the meeting start time S (minutes after 9:00)
S = Int('S')

# The meeting must be scheduled within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Add John's meeting time preference: finish by 12:00.
optimizer.add(john_preference(S))

# Helper function to ensure the meeting does not overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting [s, s+meeting_duration) must be either entirely before the busy interval or entirely after it.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Nicole has no busy times, so nothing to add.

# Add busy constraints for John.
for interval in john_busy:
    optimizer.add(no_overlap(S, interval))

# Add busy constraints for Ethan.
for interval in ethan_busy:
    optimizer.add(no_overlap(S, interval))

# To meet at the earliest possible availability, minimize S.
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