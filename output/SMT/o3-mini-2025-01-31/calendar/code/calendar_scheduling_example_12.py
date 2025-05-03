from z3 import *

# Meeting duration in minutes (60 minutes)
meeting_duration = 60

# Working hours: from 9:00 (0 minutes after 9:00) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals expressed in minutes after 9:00:

# David's busy intervals: (none)
david_busy = []

# Debra's busy intervals:
#   9:30 to 10:00   -> [30, 60)
#   11:00 to 11:30  -> [120, 150)
#   12:00 to 13:00  -> [180, 240)
#   14:00 to 14:30  -> [300, 330)
#   16:00 to 16:30  -> [420, 450)
debra_busy = [(30, 60), (120, 150), (180, 240), (300, 330), (420, 450)]

# Kevin's busy intervals:
#   9:00 to 12:00   -> [0, 180)
#   14:00 to 17:00  -> [300, 480)
kevin_busy = [(0, 180), (300, 480)]

# Combine all busy intervals from every participant.
busy_intervals = david_busy + debra_busy + kevin_busy

# Create a Z3 solver instance
solver = Solver()

# Define S as the meeting start time (in minutes after 9:00)
S = Int('S')

# The meeting must start and finish within working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# Ensure the meeting does not overlap any busy interval.
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check if there is a valid meeting time.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function: convert minutes after 9:00 (9:00 = 0) to HH:MM format.
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