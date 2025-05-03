from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (one hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 is mapped to 0 and 17:00 is mapped to 480 (minutes after 9:00)
work_start = 0
work_end = 480

# For convenience, these are the time conversions (minutes after 9:00):
# 9:00   -> 0
# 10:00  -> 60
# 11:00  -> 120
# 11:30  -> 150
# 12:00  -> 180
# 12:30  -> 210
# 14:00  -> 300
# 15:00  -> 360
# 15:30  -> 390
# 16:00  -> 420
# 17:00  -> 480

# Eric's busy interval:
# 10:00 to 12:00 -> [60, 180)
eric_busy = [(60, 180)]

# Albert's busy intervals:
# 12:00 to 12:30 -> [180, 210)
# 15:30 to 16:00 -> [390, 420)
albert_busy = [(180, 210), (390, 420)]

# Katherine's busy intervals:
# 10:00 to 11:00 -> [60, 120)
# 11:30 to 14:00 -> [150, 300)
# 15:00 to 15:30 -> [360, 390)
katherine_busy = [(60, 120), (150, 300), (360, 390)]

# Eric's preference: Do not meet after 15:30.
# Interpreting this as the meeting must be complete by 15:30.
latest_end_for_eric = 390  # 15:30 in minutes after 9:00

# Create an optimizer instance.
optimizer = Optimize()

# Define the variable S as the meeting start time (in minutes after 9:00).
S = Int('S')

# Enforce that the meeting is within work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Add Eric's preference constraint (meeting must finish by 15:30).
optimizer.add(S + meeting_duration <= latest_end_for_eric)

# Helper function to define no overlap constraint between meeting interval [s, s+duration)
# and a busy interval [busy_start, busy_end).
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting ends before the busy interval starts OR starts after the busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints to avoid overlapping with busy intervals for Eric.
for interval in eric_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints to avoid overlapping with busy intervals for Albert.
for interval in albert_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints to avoid overlapping with busy intervals for Katherine.
for interval in katherine_busy:
    optimizer.add(no_overlap(S, interval))

# To prefer the earliest possible meeting time, minimize S.
optimizer.minimize(S)

# Check and extract a solution.
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
    print("End:  ", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")