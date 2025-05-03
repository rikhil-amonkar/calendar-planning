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

# Nicholas's calendar is wide open, so no busy intervals.
nicholas_busy = []

# Elizabeth's busy intervals:
#   9:30 to 10:00   -> [time_to_minutes("9:30"), time_to_minutes("10:00")) => [30, 60)
#   11:30 to 12:00  -> [time_to_minutes("11:30"), time_to_minutes("12:00")) => [150, 180)
#   13:30 to 14:30  -> [time_to_minutes("13:30"), time_to_minutes("14:30")) => [270, 330)
#   15:00 to 15:30  -> [time_to_minutes("15:00"), time_to_minutes("15:30")) => [360, 390)
#   16:30 to 17:00  -> [time_to_minutes("16:30"), time_to_minutes("17:00")) => [450, 480)
elizabeth_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Sandra's busy intervals:
#   9:00 to 9:30   -> [time_to_minutes("9:00"), time_to_minutes("9:30")) => [0, 30)
#   10:00 to 10:30 -> [time_to_minutes("10:00"), time_to_minutes("10:30")) => [60, 90)
#   11:30 to 13:30 -> [time_to_minutes("11:30"), time_to_minutes("13:30")) => [150, 270)
#   15:30 to 16:30 -> [time_to_minutes("15:30"), time_to_minutes("16:30")) => [390, 420)
sandra_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:30"), time_to_minutes("13:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:30"))
]

# Additional constraint for Sandra: cannot meet on Monday before 13:00.
sandra_earliest = time_to_minutes("13:00")  # 13:00 corresponds to 240 minutes after 9:00.

# Create an optimizer instance from Z3.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# Add constraints: meeting must be within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Add Sandra's extra constraint: meeting cannot start before 13:00.
optimizer.add(S >= sandra_earliest)

# A helper function that returns a constraint ensuring that a meeting starting at s
# does not overlap with a given busy interval (busy_start, busy_end).
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Meeting [s, s + meeting_duration) does not overlap with busy interval [busy_start, busy_end)
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for each participant's busy intervals.
for interval in nicholas_busy:
    optimizer.add(no_overlap(S, interval))

for interval in elizabeth_busy:
    optimizer.add(no_overlap(S, interval))
    
for interval in sandra_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, we can minimize S to select the earliest possible feasible meeting time.
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