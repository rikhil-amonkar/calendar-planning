from z3 import Optimize, Int, Or, sat

# Meeting duration is 30 minutes.
meeting_duration = 30

# Define work hours in minutes relative to 9:00.
# 9:00 corresponds to 0 minutes and 17:00 corresponds to 480 minutes after 9:00.
work_start = 0
work_end = 480

# Busy intervals converted to minutes after 9:00.
# Virginia is busy from 10:00 to 12:00  -> [60, 180)
virginia_busy = [(60, 180)]

# Charles is busy:
#   12:00 to 12:30 -> [180, 210)
#   13:00 to 13:30 -> [240, 270)
charles_busy = [(180, 210), (240, 270)]

# Megan is busy:
#   9:00 to 12:00   -> [0, 180)
#   13:30 to 16:00  -> [270, 420)
#   16:30 to 17:00  -> [450, 480)
megan_busy = [(0, 180), (270, 420), (450, 480)]

# Create a Z3 Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# The meeting must start no earlier than work_start and end no later than work_end.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Add Charles's preference to avoid meetings before 14:30.
# 14:30 corresponds to 9:00 + 5.5 hours = 330 minutes after 9:00.
optimizer.add(S >= 330)

# Define a helper function to ensure that the meeting does not overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting must finish before the busy interval starts, or start after the busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Ensure the meeting does not conflict with Virginia's busy intervals.
for interval in virginia_busy:
    optimizer.add(no_overlap(S, interval))

# Ensure the meeting does not conflict with Charles's busy intervals.
for interval in charles_busy:
    optimizer.add(no_overlap(S, interval))

# Ensure the meeting does not conflict with Megan's busy intervals.
for interval in megan_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, we can minimize S to get the earliest available meeting after 14:30.
optimizer.minimize(S)

# Check if the constraints are satisfiable.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 to HH:MM formatted time.
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