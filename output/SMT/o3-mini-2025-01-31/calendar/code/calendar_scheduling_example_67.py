from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Work hours: 9:00 maps to 0 and 17:00 maps to 480 (in minutes after 9:00)
work_start = 0
work_end = 480

# Jacqueline's busy intervals (minutes after 9:00):
#   13:00 to 13:30 -> [240, 270)
#   16:00 to 16:30 -> [420, 450)
jacqueline_busy = [(240, 270), (420, 450)]

# Christian is free all day, so no busy intervals needed.

# Linda's busy intervals (minutes after 9:00):
#   9:00 to 10:30  -> [0, 90)
#   11:30 to 12:30 -> [150, 210)
#   14:00 to 14:30 -> [300, 330)
#   15:30 to 16:30 -> [390, 450)
linda_busy = [(0, 90), (150, 210), (300, 330), (390, 450)]

# Additionally, Linda cannot meet on Monday after 14:00.
# This means the meeting must finish by 14:00 (i.e. S + meeting_duration <= 300)

# Create an Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00)
S = Int('S')

# The meeting must be within the work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Enforce Linda's constraint: the meeting must finish by 14:00.
optimizer.add(S + meeting_duration <= 300)

# Helper function that returns a constraint ensuring that a meeting starting at time s
# does not overlap with a given busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting must either end before the busy period starts,
    # or start after the busy period ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for Jacqueline's busy intervals.
for interval in jacqueline_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Linda's busy intervals.
for interval in linda_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, choose the earliest valid meeting time by minimizing S.
optimizer.minimize(S)

if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Convert minutes after 9:00 to HH:MM format.
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