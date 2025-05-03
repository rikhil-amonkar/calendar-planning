from z3 import *

# Meeting duration in minutes (1 hour = 60 minutes)
meeting_duration = 60

# Working hours: from 9:00 (0 minutes) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Busy time slots represented as (start, end) in minutes after 9:00
# Arthur's busy intervals:
#   9:00 - 9:30   -> [0, 30)
#   10:30 - 12:00 -> [90, 180)   (10:30 is 90 minutes after 9:00, 12:00 is 180)
#   16:00 - 17:00 -> [420, 480)
arthur_busy = [(0, 30), (90, 180), (420, 480)]

# Michael's busy intervals:
#   13:00 - 13:30 -> [240, 270)   (13:00 is 240, 13:30 is 270)
#   14:00 - 14:30 -> [300, 330)
michael_busy = [(240, 270), (300, 330)]

# Samantha's busy intervals:
#   10:30 - 11:00 -> [90, 120)    (10:30 is 90, 11:00 is 120)
#   12:00 - 15:00 -> [180, 360)    (12:00 is 180, 15:00 is 360)
#   15:30 - 17:00 -> [390, 480)    (15:30 is 390)
samantha_busy = [(90, 120), (180, 360), (390, 480)]

# Combine all busy intervals for simplicity.
busy_intervals = arthur_busy + michael_busy + samantha_busy

# Create a Z3 solver instance.
solver = Solver()

# Define variable S representing the meeting start time (in minutes after 9:00)
S = Int('S')

# Constraint: The meeting must be within working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# For each busy interval, ensure the meeting [S, S+meeting_duration)
# does not overlap that busy interval.
for (busy_start, busy_end) in busy_intervals:
    # The meeting is either completely before the busy time or completely after.
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check if a valid meeting time exists.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration
    
    # Helper function to convert minutes after 9:00 into "HH:MM" 24-hour format.
    def minutes_to_time(m):
        total_minutes = 9 * 60 + m  # base time is 9:00
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    print("A possible meeting time is:")
    print("Start:", minutes_to_time(meeting_start))
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")