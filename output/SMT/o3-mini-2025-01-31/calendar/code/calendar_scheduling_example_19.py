from z3 import *

# Meeting duration in minutes (60 minutes)
meeting_duration = 60

# Working hours: from 9:00 (0 minutes after 9:00) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals expressed in minutes after 9:00 for each participant.

# Stephen's busy intervals:
#   10:00 to 10:30 -> [60, 90)
#   13:00 to 13:30 -> [240, 270)
#   14:30 to 15:00 -> [330, 360)
#   16:00 to 16:30 -> [420, 450)
stephen_busy = [(60, 90), (240, 270), (330, 360), (420, 450)]

# Edward's busy intervals:
#   9:00 to 9:30   -> [0, 30)
#   10:00 to 10:30 -> [60, 90)
#   13:30 to 14:30 -> [270, 330)
#   15:00 to 16:00 -> [360, 420)
edward_busy = [(0, 30), (60, 90), (270, 330), (360, 420)]

# Angela's busy intervals:
#   9:00 to 11:30   -> [0, 150)
#   12:30 to 13:00  -> [210, 240)
#   13:30 to 15:30  -> [270, 390)
#   16:00 to 17:00  -> [420, 480)
angela_busy = [(0, 150), (210, 240), (270, 390), (420, 480)]

# Combine all busy intervals.
busy_intervals = stephen_busy + edward_busy + angela_busy

# Create a Z3 solver instance.
solver = Solver()

# Define S as the start time of the meeting (in minutes after 9:00).
S = Int('S')

# The meeting must start and finish within working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# For each busy interval, ensure the meeting [S, S+meeting_duration) does not overlap with it.
for (busy_start, busy_end) in busy_intervals:
    # The meeting is either completely before the busy interval starts or completely after it ends.
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check if there is a valid meeting time.
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