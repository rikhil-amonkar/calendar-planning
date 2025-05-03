from z3 import *

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Working hours: from 9:00 (0 minutes) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals for each participant (expressed in minutes after 9:00):

# Diana's busy intervals:
#   11:30 to 12:00 -> [150, 180)
#   13:00 to 13:30 -> [240, 270)
diana_busy = [(150, 180), (240, 270)]

# Ethan has no meetings, so no busy intervals
ethan_busy = []

# Janet's busy intervals:
#   9:00 to 10:00   -> [0, 60)
#   12:30 to 13:00  -> [210, 240)
#   14:00 to 15:00  -> [300, 360)
#   15:30 to 17:00  -> [390, 480)
janet_busy = [(0, 60), (210, 240), (300, 360), (390, 480)]

# Janet's preference: the meeting must finish by (or before) 12:00, meaning:
# S + meeting_duration <= 180 (since 12:00 is 180 minutes after 9:00)

# Combine all busy intervals for all participants.
busy_intervals = diana_busy + ethan_busy + janet_busy

# Create a Z3 solver instance.
solver = Solver()

# Define S as the meeting start time (in minutes after 9:00).
S = Int('S')

# The meeting must start and finish within working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# Enforce Janet's preference (meeting must complete before 12:00).
solver.add(S + meeting_duration <= 180)

# For every busy interval, ensure that the meeting [S, S+meeting_duration) does not overlap it.
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check for a valid meeting time.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Function to convert minutes after 9:00 to HH:MM format.
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