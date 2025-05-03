from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (one hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 corresponds to 0 minutes (after 9:00), and 17:00 corresponds to 480 minutes after 9:00.
work_start = 0
work_end = 480

# Time conversion reference (minutes after 9:00):
# 9:00   -> 0
# 9:30   -> 30
# 10:00  -> 60
# 10:30  -> 90
# 11:30  -> 150
# 12:00  -> 180
# 12:30  -> 210
# 14:00  -> 300
# 14:30  -> 330 (But note: Samuel's meeting is 14:00 to 15:00 which is [300,360))
# 15:00  -> 360
# 15:30  -> 390
# 16:00  -> 420
# 16:30  -> 450
# 17:00  -> 480

# Samuel's busy intervals:
# 9:00 to 9:30   -> [0, 30)
# 10:00 to 10:30 -> [60, 90)
# 12:00 to 12:30 -> [180, 210)
# 14:00 to 15:00 -> [300, 360)
# 16:00 to 16:30 -> [420, 450)
samuel_busy = [(0, 30), (60, 90), (180, 210), (300, 360), (420, 450)]

# Emma is free all day. No busy intervals for Emma.

# Brittany's busy intervals:
# 11:30 to 14:30 -> [150, 270)
# 15:00 to 15:30 -> [360, 390)
# 16:30 to 17:00 -> [450, 480)
brittany_busy = [(150, 270), (360, 390), (450, 480)]

# Create an Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00).
S = Int('S')

# Add constraints for meeting to be within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function: ensures that meeting interval [S, S+meeting_duration) does not overlap 
# a busy interval [busy_start, busy_end)
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting should either finish before the busy period starts or start after the busy period ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Samuel's busy intervals.
for interval in samuel_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Brittany's busy intervals.
for interval in brittany_busy:
    optimizer.add(no_overlap(S, interval))

# Emma is free, so there's no need to add constraints for her schedule.

# Optionally, minimize S to choose the earliest valid time slot.
optimizer.minimize(S)

# Check if a valid meeting time exists.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration
    
    # Utility function to convert minutes-after-9:00 to HH:MM format.
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