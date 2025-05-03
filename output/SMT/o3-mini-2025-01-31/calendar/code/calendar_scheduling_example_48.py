from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (1 hour = 60 minutes)
meeting_duration = 60

# Define working hours in minutes after 9:00.
# 9:00 is 0 minutes, and 17:00 is 480 minutes.
work_start = 0
work_end = 480

# Janet's busy intervals:
#   9:30 to 10:30   -> [30, 90)
#   12:30 to 13:00  -> [210, 270)
#   14:00 to 14:30  -> [300, 330)
janet_busy = [(30, 90), (210, 270), (300, 330)]

# Rachel is free all day (no busy intervals)
rachel_busy = []

# Cynthia's busy intervals:
#   9:30 to 10:00   -> [30, 60)
#   11:00 to 11:30  -> [120, 150)
#   12:30 to 14:30  -> [210, 330)
#   16:00 to 17:00  -> [420, 480)
cynthia_busy = [(30, 60), (120, 150), (210, 330), (420, 480)]

# Create the optimizer instance.
optimizer = Optimize()

# Define the meeting start time variable (in minutes after 9:00).
S = Int('S')

# Constrain the meeting to occur within the working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Cynthia's preference: Would rather not meet before 13:30.
# Since 13:30 is 270 minutes after 9:00, enforce S >= 270.
optimizer.add(S >= 270)

# Helper function to enforce that the meeting interval [S, S+meeting_duration)
# does not overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting does not overlap with the busy interval if it finishes on or before the busy start,
    # or if it starts on or after the busy end.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Janet's busy intervals.
for interval in janet_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Cynthia's busy intervals.
for interval in cynthia_busy:
    optimizer.add(no_overlap(S, interval))

# (Rachel has no busy intervals, so no constraints are needed for her.)

# The goal is to schedule the meeting at the earliest possible time that satisfies the constraints.
optimizer.minimize(S)

# Solve and output the meeting time if a solution is found.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Convert minutes after 9:00 into HH:MM (24-hour format)
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