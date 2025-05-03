from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Define working hours in minutes after 9:00.
# 9:00 is 0 minutes, and 17:00 is 480 minutes.
work_start = 0
work_end = 480

# Teresa's busy intervals (in minutes after 9:00):
# 9:00 to 10:00    -> [0, 60)
# 13:00 to 13:30   -> [240, 270)
# 14:00 to 14:30   -> [300, 330)
# 15:00 to 15:30   -> [360, 390)
# 16:30 to 17:00   -> [450, 480)
teresa_busy = [(0, 60), (240, 270), (300, 330), (360, 390), (450, 480)]

# Kathleen's busy intervals:
# 9:00 to 9:30     -> [0, 30)
# 12:30 to 13:00   -> [210, 240)
# 13:30 to 14:00   -> [270, 300)
# 15:00 to 15:30   -> [360, 390)
kathleen_busy = [(0, 30), (210, 240), (270, 300), (360, 390)]

# Patricia's busy intervals:
# 9:00 to 10:30    -> [0, 90)
# 11:30 to 12:00   -> [150, 180)
# 13:00 to 13:30   -> [240, 270)
# 14:00 to 14:30   -> [300, 330)
# 15:30 to 16:00   -> [390, 420)
# 16:30 to 17:00   -> [450, 480)
patricia_busy = [(0, 90), (150, 180), (240, 270), (300, 330), (390, 420), (450, 480)]

# Create the Z3 Optimize instance.
optimizer = Optimize()

# Define the meeting start time variable S (in minutes after 9:00)
S = Int('S')

# Constrain the meeting to occur within working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Kathleen's preference: would rather not meet on Monday after 14:30.
# For a 30-minute meeting, ensure the meeting ends by 14:30.
# 14:30 corresponds to 330 minutes after 9:00.
optimizer.add(S + meeting_duration <= 330)

# Helper function: meeting [S, S+meeting_duration) does not overlap a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints to avoid Teresa's busy intervals.
for interval in teresa_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints to avoid Kathleen's busy intervals.
for interval in kathleen_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints to avoid Patricia's busy intervals.
for interval in patricia_busy:
    optimizer.add(no_overlap(S, interval))

# Prefer the earliest possible meeting time.
optimizer.minimize(S)

if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration
    
    # Function to convert minutes after 9:00 to HH:MM format.
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