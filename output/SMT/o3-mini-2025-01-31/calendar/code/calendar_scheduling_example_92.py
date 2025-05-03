from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (1 hour = 60 minutes)
meeting_duration = 60

# Work hours: from 9:00 (0 minutes) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Helper function to convert a time string like "9:30" to minutes after 9:00.
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return (hours - 9) * 60 + minutes

# Define busy intervals (in minutes after 9:00) for each participant

# Jacqueline's busy intervals:
#   9:30-10:00   -> [30, 60)
#   16:30-17:00  -> [450, 480)
jacqueline_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Henry is free the entire day, so no busy intervals needed.
henry_busy = []  # Henry has no busy intervals.

# William's busy intervals:
#   9:30-10:30   -> [30, 90)
#   12:30-15:00  -> [210, 360)
#   15:30-17:00  -> [390, 480)
william_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:30")),
    (time_to_minutes("12:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Create an optimizer instance from Z3.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# The meeting must be scheduled within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Function: meeting starting at s does not overlap the busy interval (b_start, b_end).
def no_overlap(s, busy_interval):
    b_start, b_end = busy_interval
    # Meeting interval: [s, s + meeting_duration)
    # The meeting does not overlap the busy interval if it ends at or before b_start, or starts at or after b_end.
    return Or(s + meeting_duration <= b_start, s >= b_end)

# Add constraints for Jacqueline's busy intervals.
for interval in jacqueline_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Henry's busy intervals (Henry is free, so no added constraints).
for interval in henry_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for William's busy intervals.
for interval in william_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, minimize S to choose the earliest feasible meeting time.
optimizer.minimize(S)

# Check if a solution exists.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Utility function to convert minutes after 9:00 back to HH:MM format.
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