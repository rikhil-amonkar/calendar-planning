from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Work hours: 9:00 maps to 0 and 17:00 maps to 480 (in minutes after 9:00)
work_start = 0
work_end = 480

# Michael's busy intervals in minutes after 9:00:
#   10:00 to 10:30 -> [60, 90)
#   11:30 to 12:00 -> [150, 180)
#   13:30 to 14:00 -> [270, 300)
#   15:30 to 16:00 -> [390, 420)
michael_busy = [(60, 90), (150, 180), (270, 300), (390, 420)]

# Bryan's calendar is free the entire day, so no busy intervals.

# Lauren's busy intervals:
#   9:00 to 10:30  -> [0, 90)
#   14:30 to 17:00 -> [330, 480)
lauren_busy = [(0, 90), (330, 480)]

# Create an Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00)
S = Int('S')

# The meeting must be scheduled within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function: returns a constraint stating that a meeting starting at time s
# does not overlap with a given busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Meeting either finishes before the busy period starts, or starts after it ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add Michael's constraints.
for interval in michael_busy:
    optimizer.add(no_overlap(S, interval))

# Add Lauren's constraints.
for interval in lauren_busy:
    optimizer.add(no_overlap(S, interval))

# For Bryan, no busy intervals are given.

# To schedule at the earliest possible time, minimize S.
optimizer.minimize(S)

# Check and get the solution.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper: Convert minutes-after-9:00 to HH:MM string.
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