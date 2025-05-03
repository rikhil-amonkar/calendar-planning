from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Define work hours: from 9:00 (0 minutes) to 17:00 (480 minutes after 9:00)
work_start = 0
work_end = 480

# Helper function to convert a time string (e.g., "10:30") to minutes after 9:00.
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return (hours - 9) * 60 + minutes

# Define busy intervals for each participant (times in minutes after 9:00).

# Austin's busy intervals:
#   10:30-11:00  -> [time_to_minutes("10:30"), time_to_minutes("11:00")) => [90, 120)
#   13:30-14:00  -> [time_to_minutes("13:30"), time_to_minutes("14:00")) => [270, 300)
austin_busy = [
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00"))
]

# Danielle's busy intervals:
#   9:00-10:00   -> [time_to_minutes("9:00"), time_to_minutes("10:00")) => [0, 60)
#   11:00-12:00  -> [time_to_minutes("11:00"), time_to_minutes("12:00")) => [120, 180)
#   13:00-13:30  -> [time_to_minutes("13:00"), time_to_minutes("13:30")) => [240, 270)
#   15:30-16:00  -> [time_to_minutes("15:30"), time_to_minutes("16:00")) => [390, 420)
danielle_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:00")),
    (time_to_minutes("11:00"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Charles' busy intervals:
#   9:00-11:30   -> [time_to_minutes("9:00"), time_to_minutes("11:30")) => [0, 150)
#   12:00-12:30  -> [time_to_minutes("12:00"), time_to_minutes("12:30")) => [180, 210)
#   13:00-17:00  -> [time_to_minutes("13:00"), time_to_minutes("17:00")) => [240, 480)
charles_busy = [
    (time_to_minutes("9:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("17:00"))
]

# Create an optimization instance using Z3.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# Ensure the meeting is scheduled within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Function that returns a constraint ensuring a meeting starting at s doesn't overlap a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting [s, s + meeting_duration) doesn't overlap with busy interval [busy_start, busy_end)
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Austin's busy times.
for interval in austin_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Danielle's busy times.
for interval in danielle_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Charles' busy times.
for interval in charles_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, choose the earliest possible meeting time by minimizing S.
optimizer.minimize(S)

# Check if a solution exists and print the result.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes-after-9:00 back to HH:MM format.
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