from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (one hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 maps to 0 and 17:00 maps to 480 (in minutes after 9:00)
work_start = 0
work_end = 480

# Busy intervals are represented as (start, end) in minutes after 9:00.

# Abigail is free the entire day, so no busy intervals.
# Michael is free the entire day, so no busy intervals.

# Sharon's busy intervals:
#   9:00 to 13:00 -> [0, 240)
#   14:00 to 17:00 -> [300, 480)
sharon_busy = [(0, 240), (300, 480)]

# Create an Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# The meeting must occur within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function to add constraints to avoid overlapping a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Enforce non-overlap conditions for Sharon's busy times.
for interval in sharon_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, choose the earliest valid meeting time by minimizing start time S.
optimizer.minimize(S)

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