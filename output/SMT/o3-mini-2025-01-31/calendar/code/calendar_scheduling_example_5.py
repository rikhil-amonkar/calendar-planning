from z3 import *

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Working hours: from 9:00 (0 minutes) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals for each participant (in minutes after 9:00):

# Kathryn's busy intervals:
#   9:00 to 9:30   -> [0, 30)
#   10:30 to 11:00 -> [90, 120)
#   11:30 to 12:00 -> [150, 180)
#   13:30 to 14:30 -> [270, 330)
#   16:30 to 17:00 -> [450, 480)
kathryn_busy = [(0, 30), (90, 120), (150, 180), (270, 330), (450, 480)]

# Charlotte's busy intervals:
#   12:00 to 12:30 -> [180, 210)
#   16:00 to 16:30 -> [420, 450)
charlotte_busy = [(180, 210), (420, 450)]

# Lauren's busy intervals:
#   9:00 to 10:00   -> [0, 60)
#   12:00 to 12:30  -> [180, 210)
#   13:30 to 14:30  -> [270, 330)
#   15:00 to 16:00  -> [360, 420)
#   16:30 to 17:00  -> [450, 480)
lauren_busy = [(0, 60), (180, 210), (270, 330), (360, 420), (450, 480)]

# Combine all busy intervals from all participants
busy_intervals = kathryn_busy + charlotte_busy + lauren_busy

# Create a Z3 solver instance.
solver = Solver()

# Define variable S representing the meeting start time (in minutes after 9:00)
S = Int('S')

# Constraint: The meeting must be scheduled within the working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# Additional constraint: Charlotte does not want the meeting after 13:30.
# 13:30 is 270 minutes after 9:00, so the meeting must finish by 13:30.
solver.add(S + meeting_duration <= 270)

# For each busy interval, ensure that the meeting [S, S+meeting_duration) does not overlap with it.
for (busy_start, busy_end) in busy_intervals:
    # Meeting is scheduled either fully before the busy interval or fully after.
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check if a valid meeting time exists.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 into a "HH:MM" 24-hour format.
    def minutes_to_time(m):
        total_minutes = 9 * 60 + m  # 9:00 AM is the baseline.
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    print("A possible meeting time is:")
    print("Start:", minutes_to_time(meeting_start))
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")