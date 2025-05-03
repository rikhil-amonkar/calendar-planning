from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Work hours: 9:00 is 0 minutes after 9:00; 17:00 is 480 minutes after 9:00.
work_start = 0
work_end = 480

# Time conversion reference:
# 9:00   -> 0
# 9:30   -> 30
# 10:00  -> 60
# 10:30  -> 90
# 11:00  -> 120
# 12:00  -> 180
# 13:00  -> 240
# 15:00  -> 360
# 15:30  -> 390
# 16:00  -> 420
# 16:30  -> 450
# 17:00  -> 480

# Michael's busy intervals:
# 9:30 to 10:30 -> [30, 90)
# 15:00 to 15:30 -> [360, 390)
# 16:00 to 16:30 -> [420, 450)
michael_busy = [(30, 90), (360, 390), (420, 450)]

# Eric's calendar is wide open, so no busy intervals.
eric_busy = []  # No constraints needed

# Arthur's busy intervals:
# 9:00 to 12:00    -> [0, 180)
# 13:00 to 15:00   -> [240, 360)
# 15:30 to 16:00   -> [390, 420)
# 16:30 to 17:00   -> [450, 480)
arthur_busy = [(0, 180), (240, 360), (390, 420), (450, 480)]

# Initialize the Z3 optimizer instance.
optimizer = Optimize()

# Define meeting start time S (in minutes after 9:00).
S = Int('S')

# Add work hour constraints.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Define a helper function to ensure that meeting [S, S+meeting_duration) does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Michael's busy intervals.
for interval in michael_busy:
    optimizer.add(no_overlap(S, interval))

# Eric has no busy intervals, so we do not add any constraints for him.

# Add constraints for Arthur's busy intervals.
for interval in arthur_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, we choose to minimize S to pick the earliest possible valid slot.
optimizer.minimize(S)

# Check if there exists a valid meeting slot.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Utility function to convert minutes-after-9:00 into HH:MM format.
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