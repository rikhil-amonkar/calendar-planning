from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Work hours: 9:00 to 17:00, represented in minutes after 9:00.
work_start = 0
work_end = 480

# Helper function to convert a time string in "HH:MM" format to minutes after 9:00.
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return (hours - 9) * 60 + minutes

# Helper function to convert minutes after 9:00 back to "HH:MM" format.
def minutes_to_time(minutes_after_nine):
    total = 9 * 60 + minutes_after_nine
    hours = total // 60
    minutes = total % 60
    return f"{hours:02d}:{minutes:02d}"

# Define busy intervals (in minutes after 9:00) for each participant.

# Jennifer's busy intervals and preference:
# Busy: 12:00 to 12:30, 16:00 to 16:30.
jennifer_busy = [
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]
# She does not want to meet on Monday before 12:30.
jennifer_earliest = time_to_minutes("12:30")

# Gary's busy intervals:
# Busy: 9:30 to 10:00, 10:30 to 11:00, 11:30 to 12:30, 14:00 to 14:30, 16:30 to 17:00.
gary_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:30")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Frances's busy intervals:
# Busy: 9:00 to 11:00, 11:30 to 12:30, 13:00 to 17:00.
frances_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("17:00"))
]

# Create an optimizer instance from Z3.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# Meeting must be within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Jennifer's preference: meeting cannot start before 12:30.
optimizer.add(S >= jennifer_earliest)

# Helper function: returns a constraint ensuring that a meeting with start s and duration
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting [s, s+meeting_duration) does not overlap with [busy_start, busy_end)
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for each busy interval.
for interval in jennifer_busy:
    optimizer.add(no_overlap(S, interval))

for interval in gary_busy:
    optimizer.add(no_overlap(S, interval))
    
for interval in frances_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, minimize S to choose the earliest possible valid meeting time.
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