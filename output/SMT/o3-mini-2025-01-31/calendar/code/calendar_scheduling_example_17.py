from z3 import *

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Working hours: from 9:00 (0 minutes after 9:00) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals expressed as minutes after 9:00.

# Margaret's busy intervals:
#   9:00 to 10:00   -> [0, 60)
#   10:30 to 11:00  -> [90, 120)
#   11:30 to 12:00  -> [150, 180)
#   13:00 to 13:30  -> [240, 270)
#   15:00 to 15:30  -> [360, 390)
margaret_busy = [(0, 60), (90, 120), (150, 180), (240, 270), (360, 390)]

# Donna's busy intervals:
#   14:30 to 15:00  -> [330, 360)
#   16:00 to 16:30  -> [420, 450)
donna_busy = [(330, 360), (420, 450)]

# Helen's busy intervals:
#   9:00 to 9:30    -> [0, 30)
#   10:00 to 11:30  -> [60, 150)
#   13:00 to 14:00  -> [240, 300)
#   14:30 to 15:00  -> [330, 360)
#   15:30 to 17:00  -> [390, 480)
helen_busy = [(0, 30), (60, 150), (240, 300), (330, 360), (390, 480)]

# Combine all busy intervals.
busy_intervals = margaret_busy + donna_busy + helen_busy

# Create a Z3 solver instance.
solver = Solver()

# Define S as the start time of the meeting (in minutes after 9:00).
S = Int('S')

# The meeting must start and end within working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# Helen does not want to meet on Monday after 13:30.
# Hence, the meeting must finish by 13:30 (which is 270 minutes after 9:00).
solver.add(S + meeting_duration <= 270)

# For every busy interval, ensure the meeting [S, S + meeting_duration) does not overlap with it.
for (busy_start, busy_end) in busy_intervals:
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