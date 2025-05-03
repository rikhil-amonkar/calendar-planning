from z3 import *

# Meeting duration: 60 minutes
meeting_duration = 60

# Working hours: 9:00 to 17:00 represented as minutes after 9:00 (0 to 480)
work_start = 0
work_end = 480

# Busy intervals for each participant (in minutes after 9:00)
# Anthony's busy intervals:
#   9:30 to 10:00 -> [30, 60)
#   12:00 to 13:00 -> [180, 240)
#   16:00 to 16:30 -> [420, 450)
anthony_busy = [(30, 60), (180, 240), (420, 450)]

# Pamela's busy intervals:
#   9:30 to 10:00 -> [30, 60)
#   16:30 to 17:00 -> [450, 480)
pamela_busy = [(30, 60), (450, 480)]

# Zachary's busy intervals:
#   9:00 to 11:30 -> [0, 150)
#   12:00 to 12:30 -> [180, 240) but note that 12:00 to 12:30 means [180, 210)
#   13:00 to 13:30 -> [240, 270)
#   14:30 to 15:00 -> [330, 360)
#   16:00 to 17:00 -> [420, 480)
zachary_busy = [(0, 150), (180, 210), (240, 270), (330, 360), (420, 480)]

# Combine all busy intervals across participants
all_busy = anthony_busy + pamela_busy + zachary_busy

# Create a Z3 solver instance
solver = Solver()

# Define S as the start time of the meeting in minutes after 9:00
S = Int('S')

# Ensure the meeting is scheduled within working hours:
solver.add(S >= work_start, S + meeting_duration <= work_end)

# Pamela's constraint: she does not want to meet after 14:30.
# That means the meeting must finish by 14:30.
# 14:30 is 5.5 hours after 9:00, i.e., 14:30 = 9:00 + 5.5*60 = 330 minutes.
solver.add(S + meeting_duration <= 330)

# For each busy interval, ensure the meeting time [S, S+meeting_duration)
# does not overlap with it.
for busy_start, busy_end in all_busy:
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