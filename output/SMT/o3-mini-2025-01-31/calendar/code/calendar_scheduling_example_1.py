from z3 import *

# Meeting duration (in minutes)
meeting_duration = 30

# Working hours: 9:00 (0) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# For Billy's preference: avoid meetings after 15:00.
# So meeting must end on or before 15:00 (i.e. S + meeting_duration <= 360, since 15:00 is 360 minutes after 9:00).
billy_meeting_end_limit = 360  # 15:00 in minutes after 9:00

# Busy time slots (in minutes after 9:00)

# Raymond's busy intervals:
#  9:00-9:30 => [0, 30)
#  11:30-12:00 => [150, 180)
#  13:00-13:30 => [240, 270)
#  15:00-15:30 => [360, 390)
raymond_busy = [(0, 30), (150, 180), (240, 270), (360, 390)]

# Billy's busy intervals:
#  10:00-10:30 => [60, 90)
#  12:00-13:00 => [180, 240)
#  16:30-17:00 => [450, 480)
billy_busy = [(60, 90), (180, 240), (450, 480)]

# Donald's busy intervals:
#  9:00-9:30  => [0, 30)
#  10:00-11:00 => [60, 120)
#  12:00-13:00 => [180, 240)
#  14:00-14:30 => [300, 330)
#  16:00-17:00 => [420, 480)
donald_busy = [(0, 30), (60, 120), (180, 240), (300, 330), (420, 480)]

# Combine all busy intervals.
busy_intervals = raymond_busy + billy_busy + donald_busy

# Create a Z3 solver instance.
solver = Solver()

# Define a variable S representing the meeting start time (in minutes after 9:00).
S = Int('S')

# Constraint: meeting must start and end within working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# Billy's preference: the meeting should end by 15:00.
solver.add(S + meeting_duration <= billy_meeting_end_limit)

# For each busy interval, ensure that the meeting [S, S + meeting_duration)
# does not overlap the busy interval.
# Two intervals [a, b) and [c, d) do not overlap if (S + meeting_duration <= busy_start)
# or (S >= busy_end).
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check if the constraints are satisfiable.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 to HH:MM format (24-hour clock).
    def minutes_to_time(m):
        total_minutes = 9 * 60 + m  # 9:00 is the base time.
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    print("A possible meeting time is:")
    print("Start:", minutes_to_time(meeting_start))
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")