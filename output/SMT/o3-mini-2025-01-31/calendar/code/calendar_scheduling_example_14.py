from z3 import *

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Working hours: from 9:00 (0 minutes after 9:00) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals expressed as minutes after 9:00.

# Brandon's busy intervals:
#   13:00 to 14:00   -> [240, 300)
#   15:30 to 16:00   -> [390, 420)
#   16:30 to 17:00   -> [450, 480)
brandon_busy = [(240, 300), (390, 420), (450, 480)]

# Jerry has no meetings the whole day.
jerry_busy = []

# Bradley's busy intervals:
#   9:00 to 11:30    -> [0, 150)
#   12:00 to 15:00   -> [180, 360)
#   16:00 to 16:30   -> [420, 450)
bradley_busy = [(0, 150), (180, 360), (420, 450)]

# Combine all busy intervals.
busy_intervals = brandon_busy + jerry_busy + bradley_busy

# Create a Z3 solver instance.
solver = Solver()

# Define S as the start time of the meeting (in minutes after 9:00).
S = Int('S')

# The meeting must start and end within working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# Brandon would like to avoid more meetings on Monday before 14:30.
# 14:30 is 5.5 hours after 9:00 -> 14:30 corresponds to 330 minutes after 9:00.
solver.add(S >= 330)

# For each busy interval, ensure that the meeting [S, S+meeting_duration) doesn't overlap with it.
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check if a valid meeting time exists.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Function to convert minutes after 9:00 to a HH:MM formatted string.
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