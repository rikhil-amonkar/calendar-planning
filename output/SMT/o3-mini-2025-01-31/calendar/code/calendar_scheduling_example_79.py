from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (one hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 is represented as 0 and 17:00 as 480 (minutes after 9:00)
work_start = 0
work_end = 480

# Time mapping (minutes after 9:00):
# 9:00   -> 0
# 10:00  -> 60
# 10:30  -> 90
# 11:00  -> 120
# 11:30  -> 150
# 12:00  -> 180
# 12:30  -> 210
# 16:00  -> 420
# 16:30  -> 450
# 17:00  -> 480

# Amy's busy intervals:
# 11:00 to 11:30 -> [120, 150)
# 12:00 to 12:30 -> [180, 210)
amy_busy = [(120, 150), (180, 210)]

# Emma has no meetings

# John's busy intervals:
# 10:00 to 10:30 -> [60, 90)
# 11:30 to 12:00 -> [150, 180)
# 12:30 to 16:00 -> [210, 420)
# 16:30 to 17:00 -> [450, 480)
john_busy = [(60, 90), (150, 180), (210, 420), (450, 480)]

# Initialize Z3 Optimize instance.
optimizer = Optimize()

# Define meeting start time S (in minutes after 9:00).
S = Int('S')

# Ensure the meeting is scheduled within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function to express non-overlap with a busy interval.
# Meeting interval [S, S + meeting_duration) must either end at or before a busy interval starts
# OR start at or after the busy interval ends.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for Amy.
for interval in amy_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for John.
for interval in john_busy:
    optimizer.add(no_overlap(S, interval))

# Emma has no restrictions.

# Optionally, minimize S to get the earliest meeting time.
optimizer.minimize(S)

if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes-after-9:00 into HH:MM format.
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