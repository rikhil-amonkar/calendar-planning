from z3 import *

# Meeting duration in minutes.
meeting_duration = 60

# Represent time as minutes from 9:00 (so 9:00 == 0, 17:00 == 480)
work_start = 0
work_end = 480

# Busy time slots for each participant (start, end) relative to 9:00
# Michelle has a meeting from 11:00 to 12:00 => [120, 180)
michelle_busy = [(120, 180)]
# Steven's busy intervals:
#  9:00 to 9:30 => [0, 30)
#  11:30 to 12:00 => [150, 180)
#  13:30 to 14:00 => [270, 300)
#  15:30 to 16:00 => [390, 420)
steven_busy = [(0, 30), (150, 180), (270, 300), (390, 420)]
# Jerry's busy intervals:
#  9:00 to 9:30  => [0, 30)
#  10:00 to 11:00 => [60, 120)
#  11:30 to 12:30 => [150, 210)
#  13:00 to 14:30 => [240, 330)
#  15:30 to 16:00 => [390, 420)
#  16:30 to 17:00 => [450, 480)
jerry_busy = [(0, 30), (60, 120), (150, 210), (240, 330), (390, 420), (450, 480)]

# Collect all busy intervals into one list.
busy_intervals = michelle_busy + steven_busy + jerry_busy

# Create a Z3 solver instance
solver = Solver()

# Define a variable S representing the start time (in minutes after 9:00)
S = Int('S')

# Constraint: meeting must be within work hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# For each busy interval, add the constraint that the meeting [S, S+60)
# must not overlap the busy interval.
#
# Non-overlap of two intervals [a,b) and [c,d) can be encoded as:
#   (S + meeting_duration <= busy_start) or (S >= busy_end)
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check if the constraints are satisfiable.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 to HH:MM format (in 24-hour time)
    def minutes_to_time(m):
        total_minutes = 9 * 60 + m  # since 9:00 is the base
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    print("A possible meeting time is:")
    print("Start:", minutes_to_time(meeting_start))
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")