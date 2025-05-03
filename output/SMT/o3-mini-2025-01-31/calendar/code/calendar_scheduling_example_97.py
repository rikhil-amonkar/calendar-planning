from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (60 minutes)
meeting_duration = 60

# Work hours: from 9:00 to 17:00 represented as minutes after 9:00.
work_start = 0
work_end = 480

# Helper function: Converts a time string "HH:MM" to minutes after 9:00.
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return (hours - 9) * 60 + minutes

# Helper function: Converts minutes after 9:00 back to a "HH:MM" time string.
def minutes_to_time(minutes_after_nine):
    total = 9 * 60 + minutes_after_nine
    hours = total // 60
    minutes = total % 60
    return f"{hours:02d}:{minutes:02d}"

# Define busy intervals for each participant (in minutes after 9:00).

# Joseph's busy intervals:
# 9:00 to 10:00, 10:30 to 11:00, 12:30 to 13:00, 14:30 to 15:30.
joseph_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:30"))
]
# Joseph does not want to meet before 14:30.
joseph_earliest = time_to_minutes("14:30")

# Kyle's busy interval:
# 12:30 to 13:30.
kyle_busy = [
    (time_to_minutes("12:30"), time_to_minutes("13:30"))
]

# Joan's busy intervals:
# 9:00 to 9:30, 10:00 to 10:30, 11:00 to 11:30, 12:30 to 14:00, 14:30 to 15:00, 15:30 to 16:00.
joan_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Create an Optimize instance from the Z3 solver.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# Meeting must fit within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Joseph prefers not to have the meeting before 14:30.
optimizer.add(S >= joseph_earliest)

# Define a helper function to ensure a meeting does not overlap a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Meeting [s, s+meeting_duration) does not overlap the busy interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Joseph's busy intervals.
for interval in joseph_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Kyle's busy intervals.
for interval in kyle_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Joan's busy intervals.
for interval in joan_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, minimize S to select the earliest valid meeting time.
optimizer.minimize(S)

# Check for a valid solution.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration
    print("A possible meeting time is:")
    print("Start:", minutes_to_time(meeting_start))
    print("End:  ", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot could be found.")