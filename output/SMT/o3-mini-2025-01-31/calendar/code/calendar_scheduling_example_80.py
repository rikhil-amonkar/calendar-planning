from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Define work hours: 9:00 is 0 minutes, 17:00 is 480 minutes (minutes after 9:00)
work_start = 0
work_end = 480

# For Alexis's preference: do not meet after 15:00.
# 15:00 is 360 minutes after 9:00, so the meeting must end by then.
max_meeting_end_for_alexis = 360

# Busy intervals for each participant (all times in minutes after 9:00):

# Michelle is busy:
# 9:30 to 10:00 -> [30, 60)
# 12:30 to 13:00 -> [210, 240)
michelle_busy = [(30, 60), (210, 240)]

# Billy is busy:
# 10:30 to 11:00 -> [90, 120)
# 11:30 to 12:00 -> [150, 180)
# 14:30 to 15:00 -> [330, 360)
# 16:00 to 16:30 -> [420, 450)
billy_busy = [(90, 120), (150, 180), (330, 360), (420, 450)]

# Alexis is busy:
# 9:30 to 10:30 -> [30, 90)
# 11:00 to 12:00 -> [120, 180)
# 12:30 to 13:00 -> [210, 240)
# 13:30 to 14:30 -> [270, 330)
# 16:00 to 16:30 -> [420, 450)
alexis_busy = [(30, 90), (120, 180), (210, 240), (270, 330), (420, 450)]

# Create an Optimize instance from Z3
optimizer = Optimize()

# Define meeting start time S (in minutes after 9:00)
S = Int('S')

# The meeting must be scheduled within the work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Alexis prefers not to meet after 15:00, so meeting must end by 15:00.
optimizer.add(S + meeting_duration <= max_meeting_end_for_alexis)

# Define a helper function that enforces that the meeting [S, S+meeting_duration)
# does not overlap with a busy interval [busy_start, busy_end)
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints so that Michelle is available.
for interval in michelle_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints so that Billy is available.
for interval in billy_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints so that Alexis is available.
for interval in alexis_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, minimize S to select the earliest possible meeting time.
optimizer.minimize(S)

# Check if a solution exists and print it.
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