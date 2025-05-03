from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (one hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 maps to 0 and 17:00 maps to 480 (in minutes after 9:00)
work_start = 0
work_end = 480

# Ronald and Maria are free all day, so no busy intervals.
# Charles' busy intervals (in minutes after 9:00):
#   9:00 to 10:30  -> [0, 90)
#   11:00 to 11:30 -> [120, 150)
#   13:30 to 14:00 -> [270, 300)
#   14:30 to 15:00 -> [330, 360)
#   15:30 to 16:30 -> [390, 450)
charles_busy = [(0, 90), (120, 150), (270, 300), (330, 360), (390, 450)]

# Create an Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# The meeting must occur within the work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function that returns a constraint enforcing that a meeting starting at time s
# does not overlap with a given busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting must finish before the busy interval begins, 
    # or start after the busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for Charles' busy intervals.
for interval in charles_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, choose the earliest valid meeting time by minimizing S.
optimizer.minimize(S)

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