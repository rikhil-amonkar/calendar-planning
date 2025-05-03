from z3 import *

# Meeting duration: 60 minutes
meeting_duration = 60

# Working hours: 9:00 to 17:00 -> represented as minutes after 9:00 (0 to 480)
work_start = 0
work_end = 480

# Busy intervals for each participant (in minutes after 9:00)
# Theresa's busy intervals:
#   9:00 to 9:30   -> [0, 30)
#   12:30 to 13:30 -> [210, 270)
#   14:00 to 15:00 -> [300, 360)
#   16:30 to 17:00 -> [450, 480)
theresa_busy = [(0, 30), (210, 270), (300, 360), (450, 480)]

# Charles's busy intervals:
#   10:00 to 10:30 -> [60, 90)
#   11:30 to 12:30 -> [150, 210)
#   14:00 to 15:30 -> [300, 390)
charles_busy = [(60, 90), (150, 210), (300, 390)]

# Betty's busy intervals:
#   9:00 to 10:30   -> [0, 90)
#   12:00 to 12:30  -> [180, 210)
#   13:00 to 14:00  -> [240, 300)
#   15:00 to 16:00  -> [360, 420)
betty_busy = [(0, 90), (180, 210), (240, 300), (360, 420)]

# Combine all busy intervals from the participants
busy_intervals = theresa_busy + charles_busy + betty_busy

# Create a Z3 solver instance
solver = Solver()

# Define S as the start time of the meeting (in minutes after 9:00)
S = Int('S')

# The meeting must be scheduled within the working hours.
solver.add(S >= work_start, S + meeting_duration <= work_end)

# For each busy interval, ensure the meeting [S, S+meeting_duration) does not overlap with it.
for (busy_start, busy_end) in busy_intervals:
    # The meeting must finish before a busy interval starts, or start after it ends.
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Find a valid meeting time slot.
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