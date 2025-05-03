from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (1 hour = 60 minutes)
meeting_duration = 60

# Define working hours: 9:00 to 17:00.
# Represent time as minutes after 9:00 (i.e., 0 to 480 minutes).
work_start = 0
work_end = 480

# Busy intervals for each participant (times represented as minutes after 9:00):

# Willie is free all day (no busy intervals).
willie_busy = []

# Richard's busy intervals:
# 10:00 to 10:30 -> [60, 90)
# 11:00 to 12:00 -> [120, 180)
# 13:00 to 14:00 -> [240, 300)
# 16:00 to 16:30 -> [420, 450)
richard_busy = [(60, 90), (120, 180), (240, 300), (420, 450)]

# Noah's busy intervals:
# 10:00 to 10:30 -> [60, 90)
# 11:30 to 13:00 -> [150, 240)
# 13:30 to 14:00 -> [270, 300)
# 14:30 to 17:00 -> [330, 480)
noah_busy = [(60, 90), (150, 240), (270, 300), (330, 480)]

# Create a Z3 Optimize instance
optimizer = Optimize()

# Define the meeting start time variable (in minutes after 9:00)
S = Int('S')

# Meeting must be scheduled within working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Define a helper function to ensure that a meeting starting at time s 
# does not overlap with a provided busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for each participant's busy intervals.

# For Willie: no busy intervals to consider.
for interval in willie_busy:
    optimizer.add(no_overlap(S, interval))

# For Richard:
for interval in richard_busy:
    optimizer.add(no_overlap(S, interval))

# For Noah:
for interval in noah_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, we can ask the solver to schedule the meeting as early as possible.
optimizer.minimize(S)

# Check if a valid meeting slot exists, and print the result.
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
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")