from z3 import Optimize, Or

# Meeting duration: 30 minutes
meeting_duration = 30

# Working hours: 9:00 to 17:00 represented in minutes after 9:00 (0 to 480)
work_start = 0
work_end = 480

# Busy intervals (in minutes after 9:00)
# Jesse's busy intervals:
#   10:00 to 10:30 -> [60, 90)
#   15:30 to 16:00 -> [390, 420)
jesse_busy = [(60, 90), (390, 420)]

# Kathryn is free all day, so no intervals.

# Megan's busy intervals:
#   10:30 to 11:00 -> [90, 120)
#   11:30 to 12:30 -> [150, 210)
#   13:30 to 14:30 -> [270, 330)
#   15:00 to 16:30 -> [360, 450)
megan_busy = [(90, 120), (150, 210), (270, 330), (360, 450)]

# Create Z3 optimizer instance to find the earliest time
optimizer = Optimize()

# Define S as the start time of the meeting in minutes after 9:00
S = Int('S')

# Add constraint that meeting must be within work hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# For Jesse's busy intervals, ensure the meeting slot does not overlap with any busy intervals.
for busy_start, busy_end in jesse_busy:
    optimizer.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# For Megan's busy intervals, ensure the meeting slot does not overlap with any busy intervals.
for busy_start, busy_end in megan_busy:
    optimizer.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# The group would like to meet at their earliest availability.
# So we minimize S.
optimizer.minimize(S)

# Check for a valid solution.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 to HH:MM format.
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