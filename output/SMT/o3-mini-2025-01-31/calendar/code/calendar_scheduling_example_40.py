from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (60 minutes)
meeting_duration = 60

# Define working hours: 9:00 to 17:00.
# We represent time as minutes after 9:00 (i.e., 0 to 480 minutes)
work_start = 0
work_end = 480

# Busy intervals for each participant (in minutes after 9:00):

# Jacob's busy intervals:
# 10:00 to 11:00  -> [60, 120)
# 11:30 to 12:00  -> [150, 180)
# 16:00 to 16:30  -> [420, 450)
jacob_busy = [(60, 120), (150, 180), (420, 450)]

# Gabriel's busy intervals:
# 9:30 to 11:30   -> [30, 150)
# 13:00 to 13:30  -> [240, 270)
# 15:00 to 15:30  -> [360, 390)
gabriel_busy = [(30, 150), (240, 270), (360, 390)]

# Matthew's busy intervals:
# 9:00 to 9:30    -> [0, 30)
# 10:30 to 11:00  -> [90, 120)
# 11:30 to 12:00  -> [150, 180)
# 12:30 to 14:00  -> [210, 300)
# 15:30 to 16:30  -> [390, 450)
matthew_busy = [(0, 30), (90, 120), (150, 180), (210, 300), (390, 450)]

# Create an optimizer (using Optimize for objective minimization)
optimizer = Optimize()

# Define the meeting start time variable in minutes after 9:00.
S = Int('S')

# The meeting must be scheduled within working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Helper function to ensure no overlap between the meeting interval [s, s+duration) and a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Meeting and the busy interval do not overlap if:
    #   meeting ends on or before busy interval starts OR meeting starts on or after busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for each participant's busy intervals.
for interval in jacob_busy:
    optimizer.add(no_overlap(S, interval))
for interval in gabriel_busy:
    optimizer.add(no_overlap(S, interval))
for interval in matthew_busy:
    optimizer.add(no_overlap(S, interval))

# We want the meeting as early as possible, so minimize S.
optimizer.minimize(S)

# Solve and print the meeting time if a solution exists.
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