from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Work hours: 9:00 is 0 minutes after 9:00; 17:00 is 480 minutes after 9:00.
work_start = 0
work_end = 480

# Time conversion reference (minutes after 9:00):
# 9:00   -> 0
# 9:30   -> 30
# 10:00  -> 60
# 11:00  -> 120
# 12:00  -> 180
# 13:00  -> 240
# 13:30  -> 270
# 14:00  -> 300
# 14:30  -> 330
# 15:00  -> 360
# 15:30  -> 390
# 16:30  -> 450
# 17:00  -> 480

# Kelly is free the entire day (no busy intervals).

# Julia's busy intervals:
# 9:30 to 10:00   -> [30, 60)
# 14:00 to 14:30  -> [300, 330)
# 15:00 to 15:30  -> [360, 390)
# 16:30 to 17:00  -> [450, 480)
julia_busy = [(30, 60), (300, 330), (360, 390), (450, 480)]

# Martha's busy intervals:
# 9:00 to 11:00   -> [0, 120)
# 12:00 to 15:00  -> [180, 360)
martha_busy = [(0, 120), (180, 360)]

# Create the Z3 optimizer instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# Add constraints for meeting to be within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Julia does not want to meet after 13:30.
# To ensure the meeting is completely before 13:30 (i.e., before 270 minutes after 9:00),
# we add the constraint that the meeting must end by 13:30.
optimizer.add(S + meeting_duration <= 270)

# Helper function: ensures that meeting interval [S, S+meeting_duration) does not overlap 
# with a busy interval [busy_start, busy_end).
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Julia's busy intervals.
for interval in julia_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Martha's busy intervals.
for interval in martha_busy:
    optimizer.add(no_overlap(S, interval))

# Kelly is free so no additional constraint is needed for her schedule.

# Optionally, we choose to minimize S to get the earliest available time.
optimizer.minimize(S)

# Check for a valid meeting slot.
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