from z3 import *

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Working hours: from 9:00 (0 minutes) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals for each participant (expressed in minutes after 9:00):

# Heather's busy intervals:
#   9:00 to 9:30   -> [0, 30)
#   10:30 to 11:00 -> [90, 120)
#   13:00 to 14:00 -> [240, 300)
#   14:30 to 15:00 -> [330, 360)
#   16:00 to 16:30 -> [420, 450)
heather_busy = [(0, 30), (90, 120), (240, 300), (330, 360), (420, 450)]

# Nicholas is free all day.
nicholas_busy = []

# Zachary's busy intervals:
#   9:00 to 10:30   -> [0, 90)
#   11:00 to 12:00  -> [120, 180)
#   12:30 to 13:00  -> [210, 240)
#   13:30 to 16:30  -> [270, 450)
zachary_busy = [(0, 90), (120, 180), (210, 240), (270, 450)]

# Additional constraint: Zachary would rather not meet on Monday after 14:00.
# This means the meeting must finish by 14:00 which is 14:00 - 9:00 = 300 minutes.
zachary_preference_end = 300

# Combine all busy intervals from participants.
busy_intervals = heather_busy + nicholas_busy + zachary_busy

# Create a Z3 solver instance.
solver = Solver()

# Define S as the meeting start time (in minutes after 9:00).
S = Int('S')

# Constraint: The meeting must start and finish within the working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# Constraint for Zachary's preference:
solver.add(S + meeting_duration <= zachary_preference_end)

# For each busy interval, ensure the meeting [S, S+meeting_duration) does not overlap it.
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check for a valid meeting time.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 into a "HH:MM" 24-hour format.
    def minutes_to_time(m):
        total_minutes = 9 * 60 + m  # baseline 9:00 AM
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    print("A possible meeting time is:")
    print("Start:", minutes_to_time(meeting_start))
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")