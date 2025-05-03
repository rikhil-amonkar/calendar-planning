from z3 import Optimize, Int, Or, sat

# Meeting duration is 60 minutes.
meeting_duration = 60

# Define working hours for Monday in minutes relative to 9:00.
# 9:00 is 0 minutes and 17:00 is 480 minutes after 9:00.
work_start = 0
work_end = 480

# Busy intervals (in minutes from 9:00) for each participant.

# Keith's busy intervals:
#   14:00 to 14:30 -> [300, 330)
#   16:00 to 16:30 -> [420, 450)
keith_busy = [(300, 330), (420, 450)]

# Christine is free the entire day, so no busy intervals.
christine_busy = []

# Cynthia's busy intervals:
#   9:00 to 10:30  -> [0, 90)
#   11:30 to 17:00 -> [270, 480)
cynthia_busy = [(0, 90), (270, 480)]

# Create a Z3 Optimize instance (using optimization to get the earliest meeting start).
optimizer = Optimize()

# Define an integer variable S representing the meeting start time in minutes after 9:00.
S = Int('S')

# The meeting must start no earlier than work_start and end no later than work_end.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Function to enforce that the meeting does not overlap a given busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Meeting is entirely before the busy interval or entirely after it.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Keith's busy intervals.
for interval in keith_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Cynthia's busy intervals.
for interval in cynthia_busy:
    optimizer.add(no_overlap(S, interval))

# Christine is free all day, so we don't add any constraints for her.

# To get the earliest possible meeting, we minimize the start time.
optimizer.minimize(S)

# Check for a solution.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 to formatted HH:MM time.
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