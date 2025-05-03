from z3 import *

# Create a solver instance
solver = Solver()

# Define the meeting start time in minutes after 9:00
meeting_start = Int('meeting_start')
meeting_duration = 30  # Meeting lasts 30 minutes

# Working hours are from 9:00 to 17:00, so the meeting must end by 17:00.
# That is, meeting_start + meeting_duration <= 480 (since 9:00 = 0 minutes, and 17:00 = 480 minutes)
solver.add(meeting_start >= 0, meeting_start + meeting_duration <= 480)

# Define a helper function to state that a meeting [meeting_start, meeting_start+duration]
# does not overlap with a busy interval [busy_start, busy_end]
def no_overlap(meeting_start, meeting_duration, busy_start, busy_end):
    meeting_end = meeting_start + meeting_duration
    return Or(meeting_end <= busy_start, meeting_start >= busy_end)

# Participant constraints

# Madison is busy during:
#   10:00 to 10:30 -> [60, 90]
#   14:30 to 15:00 -> [330, 360]
#   15:30 to 16:00 -> [390, 420]
#   16:30 to 17:00 -> [450, 480]
madison_busy = [(60, 90), (330, 360), (390, 420), (450, 480)]
for busy_start, busy_end in madison_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Linda has no meetings, so no constraints

# Logan is busy during:
#   9:00 to 12:00  -> [0, 180]
#   12:30 to 16:00 -> [210, 420]
#   16:30 to 17:00 -> [450, 480]
logan_busy = [(0, 180), (210, 420), (450, 480)]
for busy_start, busy_end in logan_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Virginia is busy during:
#   9:30 to 11:00  -> [30, 120]
#   11:30 to 12:00 -> [150, 180]
#   13:00 to 14:30 -> [240, 330]
#   15:00 to 15:30 -> [360, 390]
#   16:00 to 17:00 -> [420, 480]
virginia_busy = [(30, 120), (150, 180), (240, 330), (360, 390), (420, 480)]
for busy_start, busy_end in virginia_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Check for a valid schedule that satisfies all constraints
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()  # minutes after 9:00
    
    # Convert the start time and end time into HH:MM format
    start_hour = 9 + start_val // 60
    start_min = start_val % 60
    end_val = start_val + meeting_duration
    end_hour = 9 + end_val // 60
    end_min = end_val % 60

    print("Meeting scheduled from %02d:%02d to %02d:%02d" % (start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found.")