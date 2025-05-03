from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Define working hours: 9:00 to 17:00.
# We'll represent time as minutes after 9:00, so the window is from 0 to 480 minutes.
work_start = 0
work_end = 480

# Define the busy intervals for each participant (in minutes after 9:00).

# Albert's busy intervals:
# 9:30 to 10:30 -> [30, 90)
# 12:00 to 12:30 -> [180, 210)
# 14:00 to 14:30 -> [300, 330)
# 15:00 to 15:30 -> [360, 390)
# 16:30 to 17:00 -> [450, 480)
albert_busy = [(30, 90), (180, 210), (300, 330), (360, 390), (450, 480)]

# Gregory's busy intervals:
# 11:00 to 11:30 -> [120, 150)
# 12:30 to 13:00 -> [210, 240)
# 13:30 to 14:00 -> [270, 300)
# 15:30 to 16:00 -> [390, 420)
gregory_busy = [(120, 150), (210, 240), (270, 300), (390, 420)]

# Benjamin's busy intervals:
# 9:30 to 10:00 -> [30, 60)
# 10:30 to 11:00 -> [90, 120)
# 11:30 to 13:30 -> [150, 270)
# 14:00 to 15:00 -> [300, 360)
# 15:30 to 16:00 -> [390, 420)
# 16:30 to 17:00 -> [450, 480)
benjamin_busy = [(30, 60), (90, 120), (150, 270), (300, 360), (390, 420), (450, 480)]

# Initialize an optimizer.
optimizer = Optimize()

# Define the start time variable for the meeting (in minutes after 9:00).
S = Int('S')

# Ensure that the meeting is scheduled within the working day.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Define a helper function to add a non-overlap constraint with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting [s, s+meeting_duration) does not overlap with a busy interval
    # if it ends on or before busy_start, or starts on or after busy_end.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Albert's busy intervals.
for interval in albert_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Gregory's busy intervals.
for interval in gregory_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Benjamin's busy intervals.
for interval in benjamin_busy:
    optimizer.add(no_overlap(S, interval))

# Since the group would like to meet at their earliest availability, we minimize S.
optimizer.minimize(S)

# Check if the constraints are satisfiable, then print the solution.
if optimizer.check() == sat:
    model = optimizer.model()
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
    print("End:  ", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")