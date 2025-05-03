from z3 import *

# Meeting duration: 60 minutes
meeting_duration = 60

# Working hours: 9:00 to 17:00 represented as minutes after 9:00 (0 to 480)
work_start = 0
work_end = 480

# Busy intervals for each participant (in minutes after 9:00)

# Billy's busy intervals:
#   11:30 to 12:00 -> [150, 180)
#   13:00 to 15:00 -> [240, 360)
#   16:00 to 16:30 -> [420, 450)
billy_busy = [(150, 180), (240, 360), (420, 450)]

# Maria's busy intervals:
#   9:00 to 9:30   -> [0, 30)
#   10:00 to 10:30 -> [60, 90)
#   13:00 to 13:30 -> [240, 270)
#   14:00 to 14:30 -> [300, 330)
maria_busy = [(0, 30), (60, 90), (240, 270), (300, 330)]

# William's busy intervals:
#   9:30 to 10:00   -> [30, 60)
#   12:00 to 12:30  -> [180, 210)
#   13:30 to 15:00  -> [270, 360)
#   15:30 to 17:00  -> [390, 480)
william_busy = [(30, 60), (180, 210), (270, 360), (390, 480)]

# Combine all busy intervals from the three participants
busy_intervals = billy_busy + maria_busy + william_busy

# Create a Z3 solver instance
solver = Solver()

# Define S as the meeting start time in minutes after 9:00
S = Int('S')

# Enforce the meeting to be within working hours
solver.add(S >= work_start, S + meeting_duration <= work_end)

# For each busy interval, assert that the meeting does not overlap with it.
for busy_start, busy_end in busy_intervals:
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check if a valid meeting slot exists
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 to HH:MM format.
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