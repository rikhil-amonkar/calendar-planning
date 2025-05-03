from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Define working hours: 9:00 to 17:00.
# Represent time as minutes after 9:00, so the valid window is from 0 to 480 minutes.
work_start = 0
work_end = 480

# Isabella is free all day, but prefers not to meet after 13:00.
# We'll incorporate this preference by requiring the meeting to finish by 13:00.
# That is, meeting_end = S + meeting_duration must be <= (13:00 - 9:00)*60 = 240 minutes.
preference_end = 240

# Ronald's busy intervals (in minutes after 9:00):
# 11:30 to 12:00 -> [150, 180)
# 14:00 to 14:30 -> [300, 330)
# 16:00 to 17:00 -> [420, 480)
ronald_busy = [(150, 180), (300, 330), (420, 480)]

# Amanda's busy intervals (in minutes after 9:00):
# 9:30 to 12:00 -> [30, 180)
# 12:30 to 13:00 -> [210, 240)
# 13:30 to 14:00 -> [270, 300)
# 15:30 to 17:00 -> [390, 480)
amanda_busy = [(30, 180), (210, 240), (270, 300), (390, 480)]

# Initialize the optimizer.
optimizer = Optimize()

# Define the meeting start time variable (in minutes after 9:00).
S = Int('S')

# The meeting must be scheduled within working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Apply Isabella's preference: Meeting should finish by 13:00.
optimizer.add(S + meeting_duration <= preference_end)

# A helper function that creates a constraint for non-overlap of the meeting with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting [s, s+meeting_duration) does not overlap with busy interval if either:
    # (1) it ends on or before busy_start, or (2) it starts on or after busy_end.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for Ronald's busy intervals.
for interval in ronald_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Amanda's busy intervals.
for interval in amanda_busy:
    optimizer.add(no_overlap(S, interval))

# To satisfy the group's desire to meet at the earliest availability,
# we minimize the meeting start time S.
optimizer.minimize(S)

# Check if the constraints are satisfiable and print the result.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper: convert minutes after 9:00 to HH:MM format.
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