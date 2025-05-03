from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (1 hour = 60 minutes)
meeting_duration = 60

# Define working hours in minutes after 9:00.
# 9:00 is 0 minutes, and 17:00 is 480 minutes.
work_start = 0
work_end = 480

# David is free all day, so no busy intervals.
# Eric's busy intervals:
#   9:00 to 9:30   -> [0, 30)
#   10:30 to 11:30 -> [90, 150)
#   15:00 to 15:30 -> [360, 390)
eric_busy = [(0, 30), (90, 150), (360, 390)]

# Roger's busy intervals:
#   9:30 to 10:30   -> [30, 90)
#   11:00 to 12:00   -> [120, 180)
#   12:30 to 13:00   -> [210, 240)
#   14:30 to 15:00   -> [330, 360)
#   15:30 to 16:30   -> [390, 450)
roger_busy = [(30, 90), (120, 180), (210, 240), (330, 360), (390, 450)]

# Create an Optimize instance for Z3.
optimizer = Optimize()

# Define the meeting start time variable (in minutes after 9:00).
S = Int('S')

# Constrain the meeting to occur within the working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Helper function to ensure that the meeting interval [S, S + meeting_duration)
# does not overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Meeting does not overlap with the busy interval if it ends before the busy start
    # or it starts at/after the busy end.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Eric's busy intervals.
for interval in eric_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Roger's busy intervals.
for interval in roger_busy:
    optimizer.add(no_overlap(S, interval))

# The group would like to meet at the earliest available time.
optimizer.minimize(S)

# Check the constraints and generate the meeting time.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Function to convert minutes after 9:00 into HH:MM format.
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