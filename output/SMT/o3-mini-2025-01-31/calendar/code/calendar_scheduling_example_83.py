from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (one hour = 60 minutes)
meeting_duration = 60

# Work hours: 9:00 is 0 minutes after 9:00; 17:00 is 480 minutes after 9:00.
work_start = 0
work_end = 480

# Time conversion reference (minutes after 9:00):
# 9:00    -> 0
# 9:30    -> 30
# 10:00   -> 60
# 11:00   -> 120
# 11:30   -> 150
# 12:00   -> 180
# 12:30   -> 210
# 13:00   -> 240
# 13:30   -> 270
# 14:00   -> 300
# 14:30   -> 330
# 15:00   -> 360
# 15:30   -> 390
# 17:00   -> 480

# Anthony's busy intervals (in minutes after 9:00):
# 14:00 to 14:30 -> [300, 330)
# 15:00 to 15:30 -> [360, 390)
anthony_busy = [(300, 330), (360, 390)]

# Ronald's busy intervals:
# 9:00 to 10:00   -> [0, 60)
# 12:00 to 12:30  -> [180, 210)
# 13:30 to 14:00  -> [270, 300)
ronald_busy = [(0, 60), (180, 210), (270, 300)]

# Jonathan's busy intervals:
# 9:00 to 10:00   -> [0, 60)
# 11:00 to 11:30  -> [120, 150)
# 12:00 to 13:00  -> [180, 240)
# 14:00 to 14:30  -> [300, 330)
# 15:00 to 17:00  -> [360, 480)
jonathan_busy = [(0, 60), (120, 150), (180, 240), (300, 330), (360, 480)]

# Create an Optimize instance.
optimizer = Optimize()

# Define the meeting start time S (minutes after 9:00).
S = Int('S')

# Ensure the meeting happens during work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function: meeting [S, S+meeting_duration) must not overlap a busy interval [busy_start, busy_end)
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Anthony.
for interval in anthony_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Ronald.
for interval in ronald_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Jonathan.
for interval in jonathan_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, minimize S to pick the earliest valid slot.
optimizer.minimize(S)

# Check and extract solution.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Utility function to convert minutes-after-9:00 to HH:MM format.
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