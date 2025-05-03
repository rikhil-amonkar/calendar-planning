from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Work hours: from 9:00 to 17:00 represented as minutes after 9:00.
work_start = 0
work_end = 480

# Helper function: converts a time string "HH:MM" to minutes after 9:00.
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return (hours - 9) * 60 + minutes

# Helper function: converts minutes after 9:00 back to "HH:MM" format.
def minutes_to_time(minutes_after_nine):
    total_minutes = 9 * 60 + minutes_after_nine
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Define the busy intervals for each participant (in minutes after 9:00).

# Christopher's busy times: 
# 9:30 to 10:00, 10:30 to 11:00, 11:30 to 13:00, 15:00 to 15:30.
christopher_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("13:00")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Robert's busy times:
# 9:30 to 10:00, 11:00 to 11:30, 12:00 to 12:30, 13:30 to 14:30, 15:00 to 15:30.
robert_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Wayne's busy times:
# 10:00 to 17:00.
wayne_busy = [
    (time_to_minutes("10:00"), time_to_minutes("17:00"))
]

# Create an Optimize instance from the Z3 solver.
optimizer = Optimize()

# Define meeting start time S in minutes after 9:00.
S = Int('S')

# Ensure the meeting is within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function to ensure the meeting [s, s+duration) does not overlap a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Meeting does not overlap if it finishes before the busy interval starts
    # or starts after the busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Christopher's busy intervals.
for interval in christopher_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Robert's busy intervals.
for interval in robert_busy:
    optimizer.add(no_overlap(S, interval))
    
# Add constraints for Wayne's busy intervals.
for interval in wayne_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, minimize S to choose the earliest valid meeting time.
optimizer.minimize(S)

# Check for a solution.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration
    print("A possible meeting time is:")
    print("Start:", minutes_to_time(meeting_start))
    print("End:  ", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")