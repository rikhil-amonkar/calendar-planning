from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Work hours: 9:00 maps to 0 and 17:00 maps to 480 (in minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals are represented as (start, end) in minutes after 9:00.
# Lisa's busy intervals:
#   10:30 to 11:00 -> [90, 120)
#   11:30 to 12:00 -> [150, 180)
#   14:00 to 15:00 -> [300, 360)
lisa_busy = [(90, 120), (150, 180), (300, 360)]

# Dorothy is free all day, but her constraint is to avoid meetings beyond 10:30.
# We interpret this as the meeting must be scheduled so that it ends by 10:30.
# 10:30 is 90 minutes after 9:00.
dorothy_latest_end = 90

# Raymond's busy intervals:
#   9:00 to 10:00  -> [0, 60)
#   10:30 to 11:00 -> [90, 120)
#   11:30 to 15:00 -> [150, 300)
#   16:00 to 17:00 -> [420, 480)
raymond_busy = [(0, 60), (90, 120), (150, 300), (420, 480)]

# Create an Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# The meeting must occur within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Dorothy's constraint: meeting must end by 10:30 (i.e., within 90 minutes after 9:00).
optimizer.add(S + meeting_duration <= dorothy_latest_end)

# Helper function to add constraints to avoid overlapping a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting must either end before the busy interval starts,
    # or start after the busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Enforce non-overlap for Lisa's busy times.
for interval in lisa_busy:
    optimizer.add(no_overlap(S, interval))

# Enforce non-overlap for Raymond's busy times.
for interval in raymond_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, choose the earliest valid meeting time by minimizing start time S.
optimizer.minimize(S)

# Check if a valid meeting slot exists.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Function to convert minutes after 9:00 to HH:MM.
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