from z3 import Optimize, Int, Or, sat

# Convert meeting duration to minutes.
meeting_duration = 60

# Work hours for Monday (in minutes since 9:00).
# Monday work hours: 9:00 (0 minutes) to 17:00 (480 minutes)
work_start = 0
work_end = 480

# However, Tyler cannot meet after 16:00.
# This means that for Tyler the meeting must end by 16:00 (i.e. 420 minutes since 9:00).
# So, the meeting must end by min(work_end, 420) = 420.
tyler_meeting_end = 420

# Busy intervals for each participant (in minutes from 9:00).
# Isabella's busy intervals:
#   11:00 to 11:30 -> [120, 150)
#   15:30 to 16:00 -> [390, 420)
isabella_busy = [(120, 150), (390, 420)]

# Tyler's busy intervals:
#   9:00 to 10:00 -> [0, 60)
tyler_busy = [(0, 60)]

# Jordan's busy intervals:
#   9:00 to 10:00   -> [0, 60)
#   10:30 to 11:00  -> [90, 120)
#   12:30 to 13:30  -> [210, 270)
#   14:00 to 14:30  -> [300, 330)
#   15:00 to 16:00  -> [360, 420)
jordan_busy = [(0, 60), (90, 120), (210, 270), (300, 330), (360, 420)]

# Create a Z3 Optimize instance to also minimize the meeting start time (earliest possible meeting).
optimizer = Optimize()

# Define a variable "S" for the meeting start time in minutes from 9:00.
S = Int('S')

# Overall working hour constraints:
# The meeting must start at or after 9:00 and the meeting must finish by 17:00.
# However, Tyler's constraint forces the meeting to finish by 16:00.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= min(work_end, tyler_meeting_end))

# Function to ensure that the meeting does not overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Isabella's busy intervals.
for interval in isabella_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Tyler's busy intervals.
for interval in tyler_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Jordan's busy intervals.
for interval in jordan_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, to get the earliest possible start time, we minimize S.
optimizer.minimize(S)

# Try to find a solution.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes since 9:00 to a HH:MM time string.
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