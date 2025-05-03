from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (60 minutes)
meeting_duration = 60

# Define working hours in minutes after 9:00.
# 9:00 is 0 minutes, and 17:00 is 480 minutes.
work_start = 0
work_end = 480

# Grace's busy intervals (in minutes after 9:00):
# 9:00 to 9:30   -> [0, 30)
# 10:00 to 11:00 -> [60, 120)
# 16:00 to 16:30 -> [420, 450)
grace_busy = [(0, 30), (60, 120), (420, 450)]

# Randy's busy intervals:
# 12:30 to 13:00 -> [210, 240)
# 16:00 to 16:30 -> [420, 450)
randy_busy = [(210, 240), (420, 450)]

# Susan's busy intervals:
# 9:00 to 14:30  -> [0, 330)
# 15:30 to 16:00 -> [390, 420)
susan_busy = [(0, 330), (390, 420)]

# Create the Z3 Optimize instance.
optimizer = Optimize()

# Define the meeting start time variable S (in minutes after 9:00)
S = Int('S')

# Constrain the meeting to occur within working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Helper function: given a meeting start time s and a busy interval,
# the meeting [s, s+meeting_duration) must not overlap the busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Grace.
for interval in grace_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Randy.
for interval in randy_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Susan.
for interval in susan_busy:
    optimizer.add(no_overlap(S, interval))

# We want the earliest possible meeting time.
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