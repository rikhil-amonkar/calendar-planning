from z3 import *

# Meeting duration: 60 minutes
meeting_duration = 60

# Working hours: 9:00 to 17:00 represented as minutes after 9:00 (0 to 480)
work_start = 0
work_end = 480

# Busy intervals for each participant (in minutes after 9:00)
# Katherine and Nicole are free all day, so no busy intervals for them.

# Kevin's busy intervals:
#   9:00 to 10:00 -> [0, 60)
#   10:30 to 11:30 -> [90, 150)
#   12:00 to 15:30 -> [180, 390)
#   16:30 to 17:00 -> [450, 480)
kevin_busy = [(0, 60), (90, 150), (180, 390), (450, 480)]

# Create Z3 solver instance
solver = Solver()

# Define S as the start time of the meeting in minutes after 9:00
S = Int('S')

# Meeting must be scheduled within working hours:
solver.add(S >= work_start, S + meeting_duration <= work_end)

# For each busy interval for Kevin, ensure the meeting does not overlap with the busy times.
for busy_start, busy_end in kevin_busy:
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check if a valid meeting slot exists
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