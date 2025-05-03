from z3 import *

# Meeting duration: 60 minutes
meeting_duration = 60

# Working hours: 9:00 to 17:00 -> 0 to 480 minutes after 9:00
work_start = 0
work_end = 480

# Busy intervals for each participant, expressed in minutes after 9:00

# Bobby is free the entire day, so no busy intervals for him.

# Scott's busy intervals:
#   11:30 to 12:00 -> [150, 180)
#   15:30 to 16:00 -> [390, 420)
scott_busy = [(150, 180), (390, 420)]

# Kimberly's busy intervals:
#   11:00 to 12:00 -> [120, 180)
#   12:30 to 13:00 -> [210, 240)
#   13:30 to 14:00 -> [270, 300)
#   14:30 to 15:00 -> [330, 360)
#   15:30 to 17:00 -> [390, 480)
kimberly_busy = [(120, 180), (210, 240), (270, 300), (330, 360), (390, 480)]

# Combine all busy intervals from all participants (Bobby has none)
busy_intervals = scott_busy + kimberly_busy

# Create a Z3 solver instance
solver = Solver()

# Define S as the start time of the meeting (in minutes after 9:00)
S = Int('S')

# The meeting must start and finish within working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# For each busy interval, ensure the meeting [S, S+meeting_duration) does not overlap with it.
for (busy_start, busy_end) in busy_intervals:
    # The meeting must end before the busy interval starts, or start after the busy interval ends.
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check if there is a valid time slot.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 into HH:MM format.
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