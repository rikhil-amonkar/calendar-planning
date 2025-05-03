from z3 import Optimize, Or, Int, sat

# Meeting duration: 30 minutes
meeting_duration = 30

# Working hours: 9:00 to 17:00 represented as minutes after 9:00 (0 to 480)
work_start = 0
work_end = 480

# Busy intervals represented in minutes after 9:00.

# Richard's busy intervals:
#  13:30 to 14:00 -> [270, 300)
#  15:00 to 15:30 -> [360, 390)
richard_busy = [(270, 300), (360, 390)]

# Martha's busy intervals:
#  9:00 to 9:30 -> [0, 30)
#  13:00 to 13:30 -> [240, 270)
martha_busy = [(0, 30), (240, 270)]

# Kimberly's busy intervals:
#  9:00 to 11:00 -> [0, 120)
#  11:30 to 12:00 -> [150, 180)
#  12:30 to 13:00 -> [210, 240)
#  14:00 to 16:00 -> [300, 420)
kimberly_busy = [(0, 120), (150, 180), (210, 240), (300, 420)]

# Additional preference:
# Martha does not want to meet on Monday before 14:00.
# 14:00 is 300 minutes after 9:00.
min_meeting_start = 300

# Create a Z3 optimizer instance to find the earliest available meeting time.
optimizer = Optimize()

# Define S as the start time of the meeting in minutes after 9:00.
S = Int('S')

# The meeting must be scheduled completely within work hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Add Martha's time preference: meeting should not start before 14:00.
optimizer.add(S >= min_meeting_start)

# Add constraints so the meeting does not overlap any busy interval.

# For Richard's busy intervals:
for busy_start, busy_end in richard_busy:
    optimizer.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# For Martha's busy intervals:
for busy_start, busy_end in martha_busy:
    optimizer.add(Or(S + meeting_duration <= busy_start, S >= busy_end))
    
# For Kimberly's busy intervals:
for busy_start, busy_end in kimberly_busy:
    optimizer.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# The group would like the meeting at the earliest available time.
optimizer.minimize(S)

# Check if a valid meeting slot exists.
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
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")