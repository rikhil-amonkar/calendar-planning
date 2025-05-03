from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time in minutes after 9:00.
meeting_start = Int('meeting_start')
meeting_duration = 30  # The meeting lasts 30 minutes.

# The meeting must finish by 17:00 (i.e., 480 minutes after 9:00).
solver.add(meeting_start >= 0, meeting_start + meeting_duration <= 480)

# Helper function: The meeting interval [meeting_start, meeting_start+duration]
# must not overlap with a busy interval [busy_start, busy_end].
def no_overlap(meeting_start, meeting_duration, busy_start, busy_end):
    meeting_end = meeting_start + meeting_duration
    return Or(meeting_end <= busy_start, meeting_start >= busy_end)

# Peter's busy intervals (in minutes after 9:00):
#  9:00 to 9:30   -> [0, 30]
# 10:30 to 11:00  -> [90, 120]
# 11:30 to 12:00  -> [150, 180]
# 12:30 to 13:00  -> [210, 240]
peter_busy = [(0, 30), (90, 120), (150, 180), (210, 240)]
for start, end in peter_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, start, end))

# Judith has no busy intervals so no constraints are added for her.

# Keith's busy intervals:
# 11:30 to 12:00  -> [150, 180]
# 12:30 to 15:00  -> [210, 360]
# 15:30 to 16:00  -> [390, 420]
# 16:30 to 17:00  -> [450, 480]
keith_busy = [(150, 180), (210, 360), (390, 420), (450, 480)]
for start, end in keith_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, start, end))

# Evelyn's busy intervals:
# 9:00 to 12:30   -> [0, 210]
# 13:30 to 15:30  -> [270, 390]
# 16:30 to 17:00  -> [450, 480]
evelyn_busy = [(0, 210), (270, 390), (450, 480)]
for start, end in evelyn_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, start, end))

# Solve for a valid meeting time
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()  # minutes after 9:00

    # Convert minutes to HH:MM format
    start_hour = 9 + start_val // 60
    start_minute = start_val % 60
    end_val = start_val + meeting_duration
    end_hour = 9 + end_val // 60
    end_minute = end_val % 60

    print("Meeting scheduled from %02d:%02d to %02d:%02d" % (start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found.")