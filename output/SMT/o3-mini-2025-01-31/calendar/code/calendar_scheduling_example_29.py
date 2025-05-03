from z3 import Optimize, Or

# Meeting duration: 60 minutes (1 hour)
meeting_duration = 60

# Working hours: 9:00 to 17:00 represented as minutes after 9:00 (0 to 480)
work_start = 0
work_end = 480

# Busy intervals represented in minutes after 9:00.

# Madison's busy intervals:
#   9:30 to 10:00 -> [30, 60)
#   11:30 to 12:00 -> [150, 180)
madison_busy = [(30, 60), (150, 180)]

# Diana's busy intervals:
#   11:00 to 11:30 -> [60, 90]? WAIT: Let's recalc: 11:00 after 9:00 = 120; 11:30 = 150.
#   13:00 to 13:30 -> [240, 270)
diana_busy = [(120, 150), (240, 270)]

# Shirley's busy intervals:
#   9:00 to 12:00 -> [0, 180)
#   13:30 to 15:00 -> [270, 360)
#   15:30 to 17:00 -> [390, 480)
shirley_busy = [(0, 180), (270, 360), (390, 480)]

# Create a Z3 optimizer instance to find the earliest available meeting time.
optimizer = Optimize()

# Define S as the start time of the meeting in minutes after 9:00.
S = Int('S')

# The meeting must be scheduled completely within work hours:
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Add constraints so the meeting does not overlap any busy interval.

# For Madison's busy intervals:
for busy_start, busy_end in madison_busy:
    optimizer.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# For Diana's busy intervals:
for busy_start, busy_end in diana_busy:
    optimizer.add(Or(S + meeting_duration <= busy_start, S >= busy_end))
    
# For Shirley's busy intervals:
for busy_start, busy_end in shirley_busy:
    optimizer.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# The group would like the meeting at the earliest available time, 
# so minimize the start time S.
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