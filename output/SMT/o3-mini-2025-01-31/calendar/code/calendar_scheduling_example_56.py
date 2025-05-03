from z3 import Optimize, Int, Or, sat

# Meeting duration is 30 minutes.
meeting_duration = 30

# Define work hours in minutes relative to 9:00.
# 9:00 corresponds to 0 minutes and 17:00 corresponds to 480 minutes.
work_start = 0
work_end = 480

# Convert busy intervals to minutes after 9:00.
# Jeremy's busy intervals:
#   12:00 to 13:00  -> [180, 240)
#   13:30 to 14:00  -> [270, 300)
#   15:00 to 15:30  -> [360, 390)
jeremy_busy = [(180, 240), (270, 300), (360, 390)]

# Donna's busy intervals:
#   9:30 to 10:00   -> [30, 60)
#   13:00 to 13:30  -> [240, 270)
#   16:00 to 17:00  -> [420, 480)
donna_busy = [(30, 60), (240, 270), (420, 480)]

# Robert's busy intervals:
#   9:00 to 11:00   -> [0, 120)
#   11:30 to 12:00  -> [150, 180)
#   12:30 to 17:00  -> [210, 480)
robert_busy = [(0, 120), (150, 180), (210, 480)]

# Create the Z3 Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# The meeting must start at or after work_start and end on or before work_end.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Function to add a constraint ensuring that the meeting does not overlap a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Meeting is completely before the busy interval, or completely after.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Jeremy's busy intervals.
for interval in jeremy_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Donna's busy intervals.
for interval in donna_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Robert's busy intervals.
for interval in robert_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, minimize S to get the earliest possible meeting time.
optimizer.minimize(S)

# Check if the constraints are satisfiable and display the meeting time.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 into HH:MM format.
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