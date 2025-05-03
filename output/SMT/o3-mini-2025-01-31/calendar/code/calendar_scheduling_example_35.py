from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Define working hours: 9:00 to 17:00.
# Represent time as minutes after 9:00 (i.e., 0 to 480 minutes).
work_start = 0
work_end = 480

# Busy intervals for each participant (times represented as minutes after 9:00):

# Bradley is free all day but prefers not to meet before 14:30.
# 14:30 corresponds to 14:30 - 9:00 = 5.5 hours = 330 minutes.
bradley_earliest = 330  # Bradley's preferred start time

# Zachary's busy intervals:
# 10:00 to 10:30 -> [60, 90)
# 15:00 to 15:30 -> [360, 390)
zachary_busy = [(60, 90), (360, 390)]

# Teresa's busy intervals:
# 9:00 to 10:30 -> [0, 90)
# 11:00 to 12:30 -> [120, 150)
# 13:00 to 14:00 -> [240, 300)
# 14:30 to 16:30 -> [330, 450)
teresa_busy = [(0, 90), (120, 150), (240, 300), (330, 450)]

# Create a Z3 Optimize instance
optimizer = Optimize()

# Define the meeting start time variable (in minutes after 9:00)
S = Int('S')

# Meeting must be within working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Enforce Bradley's preference: don't meet before 14:30 (i.e., before 330 minutes)
optimizer.add(S >= bradley_earliest)

# Define a helper function to ensure that a meeting starting at time s 
# does not overlap with a provided busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting does not overlap with a busy interval if it ends before the busy interval starts 
    # or starts after the busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for each participant's busy intervals.

# Bradley has no busy intervals beyond his preference.

# For Zachary:
for interval in zachary_busy:
    optimizer.add(no_overlap(S, interval))

# For Teresa:
for interval in teresa_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, to schedule as early as possible (subject to constraints), we minimize S.
optimizer.minimize(S)

# Check if a valid meeting slot exists, and print the result.
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
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")