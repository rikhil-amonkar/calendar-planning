from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time in minutes after 9:00
meeting_start = Int('meeting_start')
meeting_duration = 60  # meeting lasts 60 minutes

# Working hours are between 9:00 and 17:00,
# so the meeting must end by 17:00 (i.e., meeting_start + 60 <= 480)
solver.add(meeting_start >= 0, meeting_start + meeting_duration <= 480)

# Helper function that encodes the condition that the meeting 
# [meeting_start, meeting_start+meeting_duration] does not overlap 
# with a busy interval [busy_start, busy_end]
def no_overlap(meeting_start, meeting_duration, busy_start, busy_end):
    meeting_end = meeting_start + meeting_duration
    # Either the meeting finishes before the busy interval starts,
    # or starts after the busy interval ends.
    return Or(meeting_end <= busy_start, meeting_start >= busy_end)

# Denise and Joseph have no meetings; hence, no constraints for them.

# Henry is busy during:
#  1) 9:00 to 9:30   --> [0, 30]
#  2) 10:00 to 10:30 --> [60, 90]
#  3) 12:00 to 14:30 --> [180, 330]
#  4) 15:00 to 16:00 --> [360, 420]
#  5) 16:30 to 17:00 --> [450, 480]
henry_busy_intervals = [(0, 30), (60, 90), (180, 330), (360, 420), (450, 480)]
for busy_start, busy_end in henry_busy_intervals:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Christian is busy during:
#  1) 9:00 to 11:00   --> [0, 120]
#  2) 14:30 to 15:30  --> [330, 390]
#  3) 16:00 to 17:00  --> [420, 480]
christian_busy_intervals = [(0, 120), (330, 390), (420, 480)]
for busy_start, busy_end in christian_busy_intervals:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Check if there is a valid meeting time
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()  # minutes after 9:00
    
    # Convert the start and end times into HH:MM for readability
    start_hour = 9 + start_val // 60
    start_min = start_val % 60
    end_val = start_val + meeting_duration
    end_hour = 9 + end_val // 60
    end_min = end_val % 60

    print("Meeting scheduled from %02d:%02d to %02d:%02d" % (start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found.")