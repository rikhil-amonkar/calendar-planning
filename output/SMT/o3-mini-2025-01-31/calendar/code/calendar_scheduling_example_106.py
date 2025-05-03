from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time in minutes after 9:00.
meeting_start = Int('meeting_start')
meeting_duration = 60  # The meeting lasts 60 minutes.

# Working hours: 9:00 to 17:00. Thus, meeting must finish by 480 minutes.
solver.add(meeting_start >= 0, meeting_start + meeting_duration <= 480)

# Helper function: Ensure that the meeting interval [start, start+duration]
# does not overlap with any busy interval [busy_start, busy_end].
def no_overlap(meeting_start, meeting_duration, busy_start, busy_end):
    meeting_end = meeting_start + meeting_duration
    return Or(meeting_end <= busy_start, meeting_start >= busy_end)

# Olivia's busy intervals:
#   12:30 to 13:30 --> [210, 270]
#   14:30 to 15:00 --> [330, 360]
#   16:30 to 17:00 --> [450, 480]
olivia_busy = [(210, 270), (330, 360), (450, 480)]
for busy_start, busy_end in olivia_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Anna has no meetings, so no constraints.

# Virginia's busy intervals:
#   9:00 to 10:00   --> [0, 60]
#   11:30 to 16:00  --> [150, 420]
#   16:30 to 17:00  --> [450, 480]
virginia_busy = [(0, 60), (150, 420), (450, 480)]
for busy_start, busy_end in virginia_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Paul's busy intervals:
#   9:00 to 9:30  --> [0, 30]
#   11:00 to 11:30 --> [120, 150]
#   13:00 to 14:00 --> [240, 300]
#   14:30 to 16:00 --> [330, 420]
#   16:30 to 17:00 --> [450, 480]
paul_busy = [(0, 30), (120, 150), (240, 300), (330, 420), (450, 480)]
for busy_start, busy_end in paul_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Check if there is a valid meeting time.
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()  # minutes after 9:00
    
    # Convert the meeting start and end times to HH:MM format.
    start_hour = 9 + start_val // 60
    start_minute = start_val % 60
    end_val = start_val + meeting_duration
    end_hour = 9 + end_val // 60
    end_minute = end_val % 60
    
    print("Meeting scheduled from %02d:%02d to %02d:%02d" % (start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found.")