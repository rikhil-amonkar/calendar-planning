from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (one hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 is represented as 0 and 17:00 as 480 (minutes after 9:00)
work_start = 0
work_end = 480

# Time mapping (minutes after 9:00):
# 9:00   -> 0
# 9:30   -> 30
# 10:00  -> 60
# 10:30  -> 90
# 11:00  -> 120
# 12:00  -> 180
# 12:30  -> 210
# 13:00  -> 240
# 13:30  -> 270
# 14:30  -> 330
# 15:00  -> 360
# 16:30  -> 450
# 17:00  -> 480

# Jacob's busy intervals on Monday:
# 9:00 to 9:30   -> [0, 30)
# 12:30 to 13:00 -> [210, 240)
# 14:30 to 15:00 -> [330, 360)
# 16:30 to 17:00 -> [450, 480)
jacob_busy = [(0, 30), (210, 240), (330, 360), (450, 480)]

# Amanda's busy intervals on Monday:
# 10:00 to 10:30 -> [60, 90)
# 12:00 to 12:30 -> [180, 210)
amanda_busy = [(60, 90), (180, 210)]

# Lisa's busy intervals on Monday:
# 11:00 to 13:00 -> [120, 180)
# 14:30 to 16:30 -> [330, 450)
lisa_busy = [(120, 180), (330, 450)]

# Create an Optimize instance to help find the earliest suitable meeting time.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# Ensure the meeting is scheduled within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Define a helper function to ensure the meeting [S, S+meeting_duration)
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for Jacob.
for interval in jacob_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Amanda.
for interval in amanda_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Lisa.
for interval in lisa_busy:
    optimizer.add(no_overlap(S, interval))

# Optimize to find the earliest possible meeting time.
optimizer.minimize(S)

# Check the constraints and extract a solution if possible.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes-after-9:00 to HH:MM format.
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