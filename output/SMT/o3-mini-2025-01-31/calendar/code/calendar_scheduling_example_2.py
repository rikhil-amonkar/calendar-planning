from z3 import *

# Meeting duration in minutes
meeting_duration = 30

# Working hours: 9:00 (0) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Amy's preference: avoid meetings after 15:30.
# Therefore the meeting must end on or before 15:30.
amy_meeting_end_limit = 390  # 15:30 in minutes after 9:00

# Busy time slots (in minutes after 9:00)

# Roy's busy intervals:
# 9:00-9:30 => [0, 30)
# 10:00-10:30 => [60, 90)
# 11:00-11:30 => [120, 150)
# 12:30-13:00 => [210, 240)
roy_busy = [(0, 30), (60, 90), (120, 150), (210, 240)]

# Kathryn's busy intervals:
# 9:30-10:00 => [30, 60)
# 16:30-17:00 => [450, 480)
kathryn_busy = [(30, 60), (450, 480)]

# Amy's busy intervals:
# 9:00-14:30 => [0, 330)
# 15:00-16:00 => [360, 420)
# 16:30-17:00 => [450, 480)
amy_busy = [(0, 330), (360, 420), (450, 480)]

# Combine all busy intervals from Roy, Kathryn, and Amy.
busy_intervals = roy_busy + kathryn_busy + amy_busy

# Create a Z3 solver instance.
solver = Solver()

# Define the variable S representing the meeting start time in minutes after 9:00.
S = Int('S')

# Constraint: meeting must begin and end within working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# Amy's preference: the meeting must finish by 15:30.
solver.add(S + meeting_duration <= amy_meeting_end_limit)

# For each busy interval, add a constraint ensuring that the meeting [S, S + meeting_duration)
# does not overlap the busy interval. Two intervals [S, S+duration) and [busy_start, busy_end)
# do not overlap if S+duration <= busy_start or S >= busy_end.
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check if a valid meeting time exists.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration
    
    # Function to convert minutes after 9:00 into HH:MM (24-hour clock).
    def minutes_to_time(m):
        total_minutes = 9 * 60 + m  # 9:00 as base time.
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    print("A possible meeting time is:")
    print("Start:", minutes_to_time(meeting_start))
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")