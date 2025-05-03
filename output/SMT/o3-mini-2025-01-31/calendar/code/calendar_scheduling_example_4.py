from z3 import *

# Meeting duration in minutes (30 mins)
meeting_duration = 30

# Working hours: from 9:00 (0 minutes) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals for each participant expressed in minutes after 9:00:

# Donna is busy:
#   14:00 to 14:30 -> [300, 330)
#   15:30 to 16:00 -> [390, 420)
donna_busy = [(300, 330), (390, 420)]

# John is busy:
#   11:00 to 11:30 -> [120, 150)
#   16:30 to 17:00 -> [450, 480)
john_busy = [(120, 150), (450, 480)]

# Billy is busy:
#   9:00 to 10:00   -> [0, 60)
#   10:30 to 14:00  -> [90, 300)
#   14:30 to 17:00  -> [330, 480)
billy_busy = [(0, 60), (90, 300), (330, 480)]

# Combine all busy intervals
busy_intervals = donna_busy + john_busy + billy_busy

# Create a Z3 solver instance.
solver = Solver()

# Define S as the meeting start time (in minutes after 9:00)
S = Int('S')

# The meeting must start and finish within working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# For every busy interval, ensure the meeting [S, S+meeting_duration) does not overlap it.
# Two intervals do not overlap if one ends before the other starts:
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Find a solution.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 into HH:MM format.
    def minutes_to_time(m):
        total_minutes = 9 * 60 + m  # Base time: 9:00
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    print("A possible meeting time is:")
    print("Start:", minutes_to_time(meeting_start))
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")