from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (one hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 is represented as 0 and 17:00 as 480 (minutes after 9:00)
work_start = 0
work_end = 480

# Time mapping (minutes after 9:00):
# 9:00    -> 0
# 10:00   -> 60
# 10:30   -> 90
# 11:00   -> 120
# 12:00   -> 180
# 12:30   -> 210
# 14:00   -> 300
# 14:30   -> 330
# 15:30   -> 390
# 16:00   -> 420
# 17:00   -> 480

# Ronald's busy intervals:
# 9:00 to 10:00  -> [0, 60)
# 11:00 to 12:00 -> [120, 180)
ronald_busy = [(0, 60), (120, 180)]

# Teresa's busy intervals:
# 10:30 to 11:00 -> [90, 120)
# 14:00 to 14:30 -> [300, 330)
teresa_busy = [(90, 120), (300, 330)]

# Carol's busy intervals:
# 9:00 to 12:30  -> [0, 210)
# 14:00 to 15:30 -> [300, 390)
# 16:00 to 17:00 -> [420, 480)
carol_busy = [(0, 210), (300, 390), (420, 480)]

# Create an Optimize instance from Z3
optimizer = Optimize()

# Define meeting start time S (in minutes after 9:00).
S = Int('S')

# Ensure the meeting is scheduled within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function to ensure no overlap with a busy interval
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Meeting [s, s+meeting_duration) does not overlap with busy [busy_start, busy_end) if:
    # it finishes at or before busy_start, or starts at or after busy_end.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add no-overlap constraints for Ronald.
for interval in ronald_busy:
    optimizer.add(no_overlap(S, interval))

# Add no-overlap constraints for Teresa.
for interval in teresa_busy:
    optimizer.add(no_overlap(S, interval))

# Add no-overlap constraints for Carol.
for interval in carol_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, minimize S to find the earliest meeting time.
optimizer.minimize(S)

# Check for a solution and print the meeting time
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Function to convert minutes-after-9:00 into HH:MM format.
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