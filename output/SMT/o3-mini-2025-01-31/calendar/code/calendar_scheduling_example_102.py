from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time in minutes after 9:00
meeting_start = Int('meeting_start')
meeting_duration = 60  # Meeting lasts 60 minutes

# Working hours: meeting must finish by 17:00 (480 minutes after 9:00)
solver.add(meeting_start >= 0, meeting_start + meeting_duration <= 480)

# Helper function to ensure the meeting interval does not overlap a busy interval.
def no_overlap(meeting_start, meeting_duration, busy_start, busy_end):
    meeting_end = meeting_start + meeting_duration
    # The meeting must end before the busy interval starts or start after it ends.
    return Or(meeting_end <= busy_start, meeting_start >= busy_end)

# Dylan is busy from 14:00 to 15:00.
# 9:00 = 0 minutes, so 14:00 = 300 and 15:00 = 360.
solver.add(no_overlap(meeting_start, meeting_duration, 300, 360))

# Kathryn is busy during:
#    9:00 to 9:30 -> [0, 30]
#    10:00 to 10:30 -> [60, 90]
solver.add(no_overlap(meeting_start, meeting_duration, 0, 30))
solver.add(no_overlap(meeting_start, meeting_duration, 60, 90))

# Hannah is busy during:
#    9:00 to 10:30 -> [0, 90]
#    12:30 to 15:30 -> [210, 390]
#    16:00 to 16:30 -> [420, 450]
hannah_busy = [(0, 90), (210, 390), (420, 450)]
for busy_start, busy_end in hannah_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Anna is busy during:
#    9:00 to 11:00  -> [0, 120]
#    12:00 to 14:00 -> [180, 300]
#    14:30 to 15:00 -> [330, 360]
#    16:00 to 16:30 -> [420, 450]
anna_busy = [(0, 120), (180, 300), (330, 360), (420, 450)]
for busy_start, busy_end in anna_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Check if a valid meeting time can be found.
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()  # minutes after 9:00

    # Convert minutes to HH:MM format
    start_hour = 9 + start_val // 60
    start_min = start_val % 60
    end_val = start_val + meeting_duration
    end_hour = 9 + end_val // 60
    end_min = end_val % 60

    print("Meeting scheduled from %02d:%02d to %02d:%02d" % (start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found.")