from z3 import *

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Working hours: from 9:00 (0 minutes) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals for each participant (expressed in minutes after 9:00):

# Diane's busy intervals:
#   9:00 to 9:30   -> [0, 30)
#   12:00 to 12:30 -> [180, 210)
#   14:30 to 15:30 -> [330, 390)
diane_busy = [(0, 30), (180, 210), (330, 390)]

# Kelly's busy intervals:
#   9:30 to 10:00 -> [30, 60)
#   10:30 to 11:00 -> [90, 120)
kelly_busy = [(30, 60), (90, 120)]

# Deborah's busy intervals:
#   9:00 to 9:30   -> [0, 30)
#   10:00 to 14:00 -> [60, 300)
#   14:30 to 17:00 -> [330, 480)
deborah_busy = [(0, 30), (60, 300), (330, 480)]

# Combine all busy intervals for all participants.
busy_intervals = diane_busy + kelly_busy + deborah_busy

# Create a Z3 solver instance.
solver = Solver()

# Define S as the meeting start time (in minutes after 9:00).
S = Int('S')

# The meeting must start and finish within working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# For every busy interval, ensure the meeting [S, S+meeting_duration) does not overlap it.
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check for a valid meeting time.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Convert minutes after 9:00 to HH:MM format
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