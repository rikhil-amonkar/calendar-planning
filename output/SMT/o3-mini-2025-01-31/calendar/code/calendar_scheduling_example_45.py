from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes
meeting_duration = 30

# Define working hours: from 9:00 to 17:00.
# We represent time as minutes after 9:00, so the valid window is from 0 to 480 minutes.
work_start = 0
work_end = 480

# Andrew and Grace are free the entire day.
# Samuel's busy intervals (in minutes after 9:00):
# 9:00 to 10:30  -> [0, 90)
# 11:30 to 12:00 -> [150, 180)
# 13:00 to 13:30 -> [240, 270)
# 14:00 to 16:00 -> [300, 420)
# 16:30 to 17:00 -> [450, 480)
samuel_busy = [(0, 90), (150, 180), (240, 270), (300, 420), (450, 480)]

# Initialize the optimizer.
optimizer = Optimize()

# Define the meeting start time variable (in minutes after 9:00).
S = Int('S')

# The meeting must be scheduled within working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Helper function to ensure the meeting [S, S+meeting_duration) does not overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for Samuel's busy intervals.
for interval in samuel_busy:
    optimizer.add(no_overlap(S, interval))

# The group would like to meet at their earliest availability therefore minimize S.
optimizer.minimize(S)

# Check if the constraints are satisfiable and print the meeting time.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Convert minutes after 9:00 into HH:MM
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