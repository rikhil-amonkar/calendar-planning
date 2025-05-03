from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Work hours: represented in minutes from 9:00.
# 9:00 maps to 0 and 17:00 maps to 480 (i.e., 8 hours later)
work_start = 0
work_end = 480

# Busy intervals are represented as (start, end) in minutes after 9:00.
# Jack's busy intervals:
#   10:30 to 11:30 -> [90, 150)
#   13:00 to 13:30 -> [240, 270)
#   14:00 to 14:30 -> [300, 330)
#   16:00 to 17:00 -> [420, 480)
jack_busy = [(90, 150), (240, 270), (300, 330), (420, 480)]

# Judith's busy intervals:
#   9:00 to 10:00   -> [0, 60)
#   10:30 to 11:00  -> [90, 120)
#   11:30 to 14:00  -> [150, 300)
#   14:30 to 15:00  -> [330, 360)
#   15:30 to 17:00  -> [390, 480)
judith_busy = [(0, 60), (90, 120), (150, 300), (330, 360), (390, 480)]

# Jeffrey is free for the entire day, but he does not want to meet before 14:00.
# 14:00 corresponds to 300 minutes (since 9:00 is 0).
jeffrey_earliest = 300

# Create an Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# Meeting must be scheduled within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Jeffrey's constraint: Meeting cannot begin before 14:00 (i.e., before 300 minutes after 9:00).
optimizer.add(S >= jeffrey_earliest)

# Helper function for non-overlapping constraints:
# It enforces that the meeting (from S to S+meeting_duration) does not overlap a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for Jack.
for interval in jack_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Judith.
for interval in judith_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, we can choose the earliest valid meeting time by minimizing S.
optimizer.minimize(S)

# Check if there exists a valid meeting slot.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 to HH:MM format.
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