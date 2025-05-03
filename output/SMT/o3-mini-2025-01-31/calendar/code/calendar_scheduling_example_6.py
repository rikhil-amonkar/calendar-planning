from z3 import *

# Meeting duration in minutes (60 minutes)
meeting_duration = 60

# Working hours: from 9:00 (0 minutes) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals for each participant expressed in minutes after 9:00:

# Thomas is free all day, so no busy intervals.
thomas_busy = []

# Dylan's busy intervals:
#   10:30 to 11:00 -> [90, 120)
#   13:30 to 14:00 -> [270, 300)
dylan_busy = [(90, 120), (270, 300)]

# Jerry's busy intervals:
#   9:00 to 11:00   -> [0, 120)
#   11:30 to 14:30  -> [150, 330)
#   16:00 to 17:00  -> [420, 480)
jerry_busy = [(0, 120), (150, 330), (420, 480)]

# Combine all busy intervals from the participants (Thomas has none)
busy_intervals = dylan_busy + jerry_busy

# Create a Z3 solver instance.
solver = Solver()

# Define S as the meeting start time (in minutes after 9:00)
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
    
    # Helper function to convert minutes after 9:00 to HH:MM format (24-hour clock).
    def minutes_to_time(m):
        total_minutes = 9 * 60 + m  # Baseline: 9:00 AM
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    print("A possible meeting time is:")
    print("Start:", minutes_to_time(meeting_start))
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")