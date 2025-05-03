from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time in minutes after 9:00 and set the meeting duration to 30 minutes.
meeting_start = Int('meeting_start')
meeting_duration = 30

# Working hours: meeting must end by 17:00 (i.e., 480 minutes after 9:00).
solver.add(meeting_start >= 0, meeting_start + meeting_duration <= 480)

# Lisa cannot meet on Monday before 14:30.
# 14:30 is 14.5 hours, which is 14.5 - 9 = 5.5 hours after 9:00.
# In minutes, that's 5.5 * 60 = 330 minutes.
solver.add(meeting_start >= 330)

# Helper function to ensure that the meeting interval [meeting_start, meeting_start+duration]
# does not overlap a given busy interval [busy_start, busy_end].
def no_overlap(meeting_start, meeting_duration, busy_start, busy_end):
    meeting_end = meeting_start + meeting_duration
    return Or(meeting_end <= busy_start, meeting_start >= busy_end)

# Lisa's busy intervals (in minutes after 9:00):
#  9:00 to 9:30   -> [0, 30]
# 10:00 to 10:30  -> [60, 90]
# 13:00 to 14:00  -> [240, 300]
# 15:00 to 16:00  -> [360, 420]
lisa_busy = [(0, 30), (60, 90), (240, 300), (360, 420)]
for busy_start, busy_end in lisa_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Dorothy's busy intervals:
#  9:00 to 9:30    -> [0, 30]
# 10:30 to 11:30   -> [90, 150]
# 13:30 to 14:00   -> [270, 300]
# 14:30 to 15:30   -> [330, 390]
dorothy_busy = [(0, 30), (90, 150), (270, 300), (330, 390)]
for busy_start, busy_end in dorothy_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Anthony's busy intervals:
#  9:00 to 10:00    -> [0, 60]
# 11:00 to 12:30    -> [120, 210]
# 13:00 to 14:00    -> [240, 300]
# 15:00 to 16:30    -> [360, 450]
anthony_busy = [(0, 60), (120, 210), (240, 300), (360, 450)]
for busy_start, busy_end in anthony_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Ryan's busy intervals:
#  9:00 to 12:30    -> [0, 210]
# 13:00 to 16:30    -> [240, 450]
ryan_busy = [(0, 210), (240, 450)]
for busy_start, busy_end in ryan_busy:
    solver.add(no_overlap(meeting_start, meeting_duration, busy_start, busy_end))

# Check if there is a valid meeting time that meets all constraints.
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()  # meeting start in minutes after 9:00
    
    # Compute the meeting's end time.
    end_val = start_val + meeting_duration
    
    # Convert times to HH:MM format.
    start_hour = 9 + start_val // 60
    start_minute = start_val % 60
    end_hour = 9 + end_val // 60
    end_minute = end_val % 60
    
    print("Meeting scheduled from %02d:%02d to %02d:%02d" % 
          (start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found.")