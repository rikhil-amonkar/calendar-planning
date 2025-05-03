from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time in minutes after 9:00
meeting_start = Int('meeting_start')
meeting_duration = 30  # Meeting lasts 30 minutes

# Working hours: meeting must finish by 17:00.
# Since 9:00 corresponds to 0 minutes and 17:00 corresponds to 480 minutes:
solver.add(meeting_start >= 0, meeting_start + meeting_duration <= 480)

# Helper function to ensure the meeting interval does not overlap a busy interval
def no_overlap(meeting_start, meeting_duration, busy_start, busy_end):
    meeting_end = meeting_start + meeting_duration
    return Or(meeting_end <= busy_start, meeting_start >= busy_end)

# Diane is busy during:
#   9:30 to 10:00 -> [30, 60]
#   14:30 to 15:00 -> [330, 360]
diane_busy = [(30, 60), (330, 360)]
for busy_start, busy_end in diane_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Jack is busy during:
#   13:30 to 14:00 -> [270, 300]
#   14:30 to 15:00 -> [330, 360]
jack_busy = [(270, 300), (330, 360)]
for busy_start, busy_end in jack_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Eugene is busy during:
#   9:00 to 10:00 -> [0, 60]
#   10:30 to 11:30 -> [90, 150]
#   12:00 to 14:30 -> [180, 330]
#   15:00 to 16:30 -> [360, 510]
eugene_busy = [(0, 60), (90, 150), (180, 330), (360, 510)]
for busy_start, busy_end in eugene_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Patricia is busy during:
#   9:30 to 10:30 -> [30, 90]
#   11:00 to 12:00 -> [120, 180]
#   12:30 to 14:00 -> [210, 300]
#   15:00 to 16:30 -> [360, 510]
patricia_busy = [(30, 90), (120, 180), (210, 300), (360, 510)]
for busy_start, busy_end in patricia_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Check if the constraints yield a valid meeting time
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()  # minutes after 9:00

    # Convert the start and end times into HH:MM format
    start_hour = 9 + start_val // 60
    start_min = start_val % 60
    end_val = start_val + meeting_duration
    end_hour = 9 + end_val // 60
    end_min = end_val % 60

    print("Meeting scheduled from %02d:%02d to %02d:%02d" % (start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found.")