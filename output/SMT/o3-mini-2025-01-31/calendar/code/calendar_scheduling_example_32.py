from z3 import Optimize, Or, Int, sat

# Meeting duration in minutes
meeting_duration = 30

# Define working hours from 9:00 to 17:00.
# Represent time as minutes after 9:00. So 9:00 -> 0 and 17:00 -> 480.
work_start = 0
work_end = 480

# Busy intervals for each participant, expressed in minutes after 9:00.
# Emily's busy intervals:
# 10:00 to 10:30  -> [60, 90)
# 11:30 to 12:30  -> [150, 210)
# 14:00 to 15:00  -> [300, 360)
# 16:00 to 16:30  -> [420, 450)
emily_busy = [(60, 90), (150, 210), (300, 360), (420, 450)]

# Melissa's busy intervals:
# 9:30 to 10:00   -> [30, 60)
# 14:30 to 15:00  -> [330, 360)
melissa_busy = [(30, 60), (330, 360)]

# Frank's busy intervals:
# 10:00 to 10:30  -> [60, 90)
# 11:00 to 11:30  -> [120, 150)
# 12:30 to 13:00  -> [210, 240)
# 13:30 to 14:30  -> [270, 330)
# 15:00 to 16:00  -> [360, 420)
# 16:30 to 17:00  -> [450, 480)
frank_busy = [(60, 90), (120, 150), (210, 240), (270, 330), (360, 420), (450, 480)]

# Additional preference:
# Frank does not want to meet on Monday after 9:30.
# We interpret this as requiring that the meeting start time is at or before 9:30.
# In minutes after 9:00, 9:30 corresponds to 30 minutes.
max_meeting_start_for_frank = 30

# Create a Z3 Optimize instance.
optimizer = Optimize()

# Define the meeting's start time variable (in minutes after 9:00).
S = Int('S')

# The meeting must be completely within the workday.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Frank's preference: meeting should not start after 9:30.
optimizer.add(S <= max_meeting_start_for_frank)

# Utility: function to add non-overlapping constraint between the meeting and a busy interval.
def no_overlap(s, busy_interval):
    start_busy, end_busy = busy_interval
    return Or(s + meeting_duration <= start_busy, s >= end_busy)

# Add constraints for each participant to avoid their busy intervals.

for busy in emily_busy:
    optimizer.add(no_overlap(S, busy))

for busy in melissa_busy:
    optimizer.add(no_overlap(S, busy))

for busy in frank_busy:
    optimizer.add(no_overlap(S, busy))

# We want to schedule at the earliest available time.
optimizer.minimize(S)

# Solve for a valid time slot.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes (from 9:00) to HH:MM format.
    def minutes_to_time(minutes_after_nine):
        total_minutes = 9 * 60 + minutes_after_nine
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    print("A possible meeting time is:")
    print("Start:", minutes_to_time(meeting_start))
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")