from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time in minutes after 9:00.
meeting_start = Int('meeting_start')
meeting_duration = 30  # The meeting lasts 30 minutes.

# Working hours are 9:00 to 17:00, so the meeting must end by 17:00.
# Since 9:00 is 0 minutes and 17:00 is 480 minutes:
solver.add(meeting_start >= 0, meeting_start + meeting_duration <= 480)

# Helper function to ensure the meeting interval does not overlap a busy interval.
def no_overlap(meeting_start, meeting_duration, busy_start, busy_end):
    meeting_end = meeting_start + meeting_duration
    # Ensure the meeting ends before the busy interval starts or starts after it ends.
    return Or(meeting_end <= busy_start, meeting_start >= busy_end)

# Jason's busy intervals:
#   9:00 to 10:00 -> [0, 60]
#   10:30 to 11:00 -> [90, 120]
#   11:30 to 12:00 -> [150, 180]
#   12:30 to 13:00 -> [210, 240]
#   14:00 to 14:30 -> [300, 330]
jason_busy = [(0, 60), (90, 120), (150, 180), (210, 240), (300, 330)]
for busy_start, busy_end in jason_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# William's busy intervals:
#   9:00 to 9:30 -> [0, 30]
#   11:30 to 12:00 -> [150, 180]
#   14:00 to 14:30 -> [300, 330]
#   16:30 to 17:00 -> [450, 480]
william_busy = [(0, 30), (150, 180), (300, 330), (450, 480)]
for busy_start, busy_end in william_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Frances's busy intervals:
#   9:00 to 9:30 -> [0, 30]
#   10:00 to 10:30 -> [60, 90]
#   11:00 to 12:30 -> [120, 210]
#   13:30 to 16:00 -> [270, 420]
frances_busy = [(0, 30), (60, 90), (120, 210), (270, 420)]
for busy_start, busy_end in frances_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Rachel's busy intervals:
#   9:00 to 9:30 -> [0, 30]
#   10:00 to 10:30 -> [60, 90]
#   11:00 to 14:00 -> [120, 300]
#   14:30 to 16:00 -> [330, 420]
#   16:30 to 17:00 -> [450, 480]
rachel_busy = [(0, 30), (60, 90), (120, 300), (330, 420), (450, 480)]
for busy_start, busy_end in rachel_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Determine if there is a valid meeting time.
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()  # minutes after 9:00
    
    # Convert the start and end times to HH:MM format.
    start_hour = 9 + start_val // 60
    start_minute = start_val % 60
    end_val = start_val + meeting_duration
    end_hour = 9 + end_val // 60
    end_minute = end_val % 60
    
    print("Meeting scheduled from %02d:%02d to %02d:%02d" % (start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found.")