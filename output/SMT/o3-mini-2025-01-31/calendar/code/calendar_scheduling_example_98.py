from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Work hours: from 9:00 to 17:00 represented as minutes after 9:00.
work_start = 0
work_end = 480  # 17:00 is 480 minutes after 9:00

# Helper function: Converts a time string "HH:MM" to minutes after 9:00.
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return (hours - 9) * 60 + minutes

# Helper function: Converts minutes after 9:00 back to a "HH:MM" time string.
def minutes_to_time(minutes_after_nine):
    total_minutes = 9 * 60 + minutes_after_nine
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Define busy intervals for each participant in minutes after 9:00.

# Juan's busy intervals: 9:00-10:30 and 15:30-16:00.
juan_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:30")),  # (0, 90)
    (time_to_minutes("15:30"), time_to_minutes("16:00"))    # (390, 420)
]
# Additionally, Juan cannot meet after 16:00, so his meeting must end by 16:00.
# This means: S + meeting_duration <= time_to_minutes("16:00"), i.e., S + 30 <= 420.

# Marilyn's busy intervals: 11:00-11:30 and 12:30-13:00.
marilyn_busy = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),  # (120, 150)
    (time_to_minutes("12:30"), time_to_minutes("13:00"))     # (210, 240)
]

# Ronald's busy intervals: 9:00-10:30, 12:00-12:30, 13:00-13:30, 14:00-16:30.
ronald_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:30")),   # (0, 90)
    (time_to_minutes("12:00"), time_to_minutes("12:30")),  # (180, 210)
    (time_to_minutes("13:00"), time_to_minutes("13:30")),  # (240, 270)
    (time_to_minutes("14:00"), time_to_minutes("16:30"))   # (300, 450)
]

# Create an Optimize instance from the Z3 solver.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# The meeting must be scheduled within the overall work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Juan cannot have his meeting end after 16:00.
optimizer.add(S + meeting_duration <= time_to_minutes("16:00"))  # S + 30 <= 420

# Helper function to ensure the meeting [S, S+meeting_duration)
# does not overlap a given busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Juan's busy intervals.
for interval in juan_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Marilyn's busy intervals.
for interval in marilyn_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Ronald's busy intervals.
for interval in ronald_busy:
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