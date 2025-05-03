from z3 import *

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Working hours: from 9:00 (0 minutes after 9:00) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals expressed as minutes after 9:00.

# Brian has no meetings, so nothing to add.

# Billy's busy intervals:
#   10:00 to 10:30 -> [60, 90)
#   11:30 to 12:00 -> [150, 180)
#   14:00 to 14:30 -> [300, 330)
#   16:30 to 17:00 -> [450, 480)
billy_busy = [(60, 90), (150, 180), (300, 330), (450, 480)]

# Patricia's busy intervals:
#   9:00 to 12:30   -> [0, 210)
#   13:30 to 14:00  -> [270, 300)
#   14:30 to 16:00  -> [330, 420)
#   16:30 to 17:00  -> [450, 480)
patricia_busy = [(0, 210), (270, 300), (330, 420), (450, 480)]

# Combine all busy intervals.
busy_intervals = billy_busy + patricia_busy

# Create a Z3 solver instance.
solver = Solver()

# Define S as the start time of the meeting (in minutes after 9:00).
S = Int('S')

# The meeting must start and end within working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# Billy would like to avoid meetings after 15:30.
# Therefore, the meeting should finish by or before 15:30 (which is 390 minutes after 9:00).
solver.add(S + meeting_duration <= 390)

# For every busy interval, ensure the meeting [S, S + meeting_duration) does not overlap with it.
for (busy_start, busy_end) in busy_intervals:
    # The meeting either finishes before the busy interval starts, or starts after the busy interval ends.
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check if there's a valid meeting time.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function: Convert minutes after 9:00 to HH:MM format.
    def minutes_to_time(minutes_after_nine):
        total_minutes = 9 * 60 + minutes_after_nine
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    print("A possible meeting time is:")
    print("Start:", minutes_to_time(meeting_start))
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")