from z3 import Optimize, Or

# Meeting duration: 30 minutes
meeting_duration = 30

# Working hours: 9:00 to 17:00 represented in minutes after 9:00 (0 to 480)
work_start = 0
work_end = 480

# Busy intervals are represented as (start, end) in minutes after 9:00.

# Brittany's busy intervals:
#   13:00 to 13:30 -> [240, 270)
#   16:00 to 16:30 -> [420, 450)
brittany_busy = [(240, 270), (420, 450)]

# Emily is free all day, so no constraints.

# Doris's busy intervals:
#   9:00 to 11:00 -> [0, 120)
#   11:30 to 14:30 -> [150, 330)
#   15:00 to 17:00 -> [360, 480)
doris_busy = [(0, 120), (150, 330), (360, 480)]

# Create a Z3 optimizer instance to find the earliest available meeting time.
optimizer = Optimize()

# Define S as the start time of the meeting in minutes after 9:00.
S = Int('S')

# Constraint: the meeting must be scheduled completely within work hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Add constraints for Brittany's busy intervals: the meeting must not overlap any busy interval.
for busy_start, busy_end in brittany_busy:
    optimizer.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Add constraints for Doris's busy intervals.
for busy_start, busy_end in doris_busy:
    optimizer.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# The group would like to schedule the meeting at the earliest availability.
optimizer.minimize(S)

# Check if a valid meeting time exists.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # A helper function to convert minutes after 9:00 into HH:MM format.
    def minutes_to_time(minutes_after_nine):
        total_minutes = 9 * 60 + minutes_after_nine
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    print("A possible meeting time is:")
    print("Start:", minutes_to_time(meeting_start))
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")