from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Define working hours: 9:00 to 17:00.
# Represent time as minutes after 9:00, so the window is from 0 to 480 minutes.
work_start = 0
work_end = 480

# Define participant busy intervals in minutes after 9:00.
# Nancy's busy intervals:
# 11:00 to 12:30 -> [120, 210)
# 13:00 to 13:30 -> [240, 270)
# 14:00 to 15:00 -> [300, 360)
nancy_busy = [(120, 210), (240, 270), (300, 360)]

# Patricia's busy intervals:
# 10:00 to 12:00 -> [60, 180)
# 12:30 to 13:00 -> [210, 240)
# 13:30 to 16:00 -> [270, 420)
patricia_busy = [(60, 180), (210, 240), (270, 420)]

# Alan's calendar is wide open,
# but he prefers no meeting before 14:30 (14:30 - 9:00 = 330 minutes).
alan_preference_start = 330

# Initialize an optimizer.
optimizer = Optimize()

# Define the meeting start time variable (in minutes after 9:00).
S = Int('S')

# Ensure the meeting is within working hours and respects Alan's preference.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)
optimizer.add(S >= alan_preference_start)

# Helper function that returns a constraint stating that the meeting
# interval [S, S+meeting_duration) does not overlap a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # The meeting does not overlap the busy interval if it ends before or when
    # the busy interval starts, or if it starts after or when the busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for Nancy's busy intervals.
for interval in nancy_busy:
    optimizer.add(no_overlap(S, interval))
    
# Add non-overlap constraints for Patricia's busy intervals.
for interval in patricia_busy:
    optimizer.add(no_overlap(S, interval))

# We want to have the meeting as early as possible,
# so we minimize the meeting start time S.
optimizer.minimize(S)

# Check if our constraints are satisfiable and output the result.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Function to convert minutes-after-9:00 to HH:MM format.
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