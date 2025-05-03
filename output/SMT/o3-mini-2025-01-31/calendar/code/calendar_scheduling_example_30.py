from z3 import Optimize, Or, Int, sat

# Meeting duration: 30 minutes
meeting_duration = 30

# Working hours: 9:00 to 17:00 represented as minutes after 9:00 (0 to 480)
work_start = 0
work_end = 480

# Busy intervals represented in minutes after 9:00.

# Jeffrey's busy intervals:
#  9:30 to 10:00 -> [30, 60)
#  10:30 to 11:00 -> [90, 120)
jeffrey_busy = [(30, 60), (90, 120)]

# Virginia's busy intervals:
#  9:00 to 9:30 -> [0, 30)
#  10:00 to 10:30 -> [60, 90)
#  14:30 to 15:00 -> [330, 360)
#  16:00 to 16:30 -> [420, 450)
virginia_busy = [(0, 30), (60, 90), (330, 360), (420, 450)]

# Melissa's busy intervals:
#  9:00 to 11:30 -> [0, 150)
#  12:00 to 12:30 -> [180, 210)
#  13:00 to 15:00 -> [240, 360)
#  16:00 to 17:00 -> [420, 480)
melissa_busy = [(0, 150), (180, 210), (240, 360), (420, 480)]

# Additional preference: Melissa would rather not meet on Monday after 14:00.
# 14:00 in minutes after 9:00 is 300.
# We add a constraint so that the meeting must start before 14:00.
additional_constraint = 300  # meeting must start before 300

# Create a Z3 optimizer instance to find the earliest available meeting time.
optimizer = Optimize()

# Define S as the start time of the meeting in minutes after 9:00.
S = Int('S')

# The meeting must be scheduled completely within work hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Add the additional preference constraint for Melissa:
optimizer.add(S < additional_constraint)

# Add constraints so the meeting does not overlap any busy interval.

# For Jeffrey's busy intervals:
for busy_start, busy_end in jeffrey_busy:
    optimizer.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# For Virginia's busy intervals:
for busy_start, busy_end in virginia_busy:
    optimizer.add(Or(S + meeting_duration <= busy_start, S >= busy_end))
    
# For Melissa's busy intervals:
for busy_start, busy_end in melissa_busy:
    optimizer.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# The group would like the meeting at the earliest available time.
optimizer.minimize(S)

# Check if a valid meeting slot exists.
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