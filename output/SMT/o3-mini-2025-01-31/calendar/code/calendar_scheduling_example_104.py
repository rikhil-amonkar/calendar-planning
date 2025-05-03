from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time in minutes after 9:00.
meeting_start = Int('meeting_start')
meeting_duration = 30  # The meeting lasts 30 minutes.

# Working hours are 9:00 to 17:00, so the meeting must finish by 17:00.
# Since 9:00 is 0 minutes and 17:00 is 480 minutes, we have:
solver.add(meeting_start >= 0, meeting_start + meeting_duration <= 480)

# Helper function: meeting [start, start+duration] must not overlap busy interval [busy_start, busy_end].
def no_overlap(meeting_start, meeting_duration, busy_start, busy_end):
    meeting_end = meeting_start + meeting_duration
    return Or(meeting_end <= busy_start, meeting_start >= busy_end)

# Karen's busy intervals:
#   9:00 to 10:30 --> [0, 90]
#   16:30 to 17:00 --> [450, 480]
karen_busy = [(0, 90), (450, 480)]
for start, end in karen_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, start, end))

# Brandon's busy intervals:
#   9:30 to 10:00  --> [30, 60]
#   10:30 to 11:00 --> [90, 120]
#   11:30 to 12:30 --> [150, 210]
#   15:30 to 16:00 --> [390, 420]
#   16:30 to 17:00 --> [450, 480]
brandon_busy = [(30, 60), (90, 120), (150, 210), (390, 420), (450, 480)]
for start, end in brandon_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, start, end))

# Donald's busy intervals:
#   9:00 to 10:30  --> [0, 90]
#   11:00 to 14:00 --> [120, 300]
#   14:30 to 17:00 --> [330, 480]
donald_busy = [(0, 90), (120, 300), (330, 480)]
for start, end in donald_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, start, end))

# Kelly's busy intervals:
#   9:00 to 9:30   --> [0, 30]
#   10:30 to 11:00 --> [90, 120]
#   11:30 to 12:00 --> [150, 180]
#   13:30 to 14:00 --> [270, 300]
#   14:30 to 15:30 --> [330, 390]
#   16:00 to 17:00 --> [420, 480]
kelly_busy = [(0, 30), (90, 120), (150, 180), (270, 300), (330, 390), (420, 480)]
for start, end in kelly_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, start, end))

# Check if there is a valid meeting time satisfying all constraints.
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