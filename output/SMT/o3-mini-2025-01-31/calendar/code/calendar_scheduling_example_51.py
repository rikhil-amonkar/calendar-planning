from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (60 minutes)
meeting_duration = 60

# Define working hours in minutes after 9:00.
# 9:00 is 0 minutes, and 17:00 is 480 minutes.
work_start = 0
work_end = 480

# Brandon's busy intervals (in minutes after 9:00):
# 11:30 to 12:00 -> [150, 180)
# 12:30 to 13:30 -> [210, 270)
# 14:00 to 14:30 -> [300, 330)
brandon_busy = [(150, 180), (210, 270), (300, 330)]

# Donna's busy intervals:
# 10:00 to 10:30 -> [60, 90)
# 12:00 to 12:30 -> [180, 210)
donna_busy = [(60, 90), (180, 210)]

# Jack's busy intervals:
# 9:30 to 10:00   -> [30, 60)
# 10:30 to 11:00  -> [90, 120)
# 11:30 to 12:30  -> [150, 210)
# 13:00 to 14:30  -> [240, 330)
# 15:30 to 17:00  -> [390, 480)
jack_busy = [(30, 60), (90, 120), (150, 210), (240, 330), (390, 480)]

# Create the Z3 Optimize instance.
optimizer = Optimize()

# Define the meeting start time variable S (in minutes after 9:00)
S = Int('S')

# Constrain the meeting to occur within working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Helper function: meeting interval [S, S+meeting_duration) does not overlap a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Meeting must end before the busy interval starts or start after it ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints to avoid Brandon's busy intervals.
for interval in brandon_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints to avoid Donna's busy intervals.
for interval in donna_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints to avoid Jack's busy intervals.
for interval in jack_busy:
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