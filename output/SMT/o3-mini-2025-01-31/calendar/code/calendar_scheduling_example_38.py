from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Define working hours: 9:00 to 17:00.
# We represent time as minutes after 9:00 (i.e., 0 to 480 minutes).
work_start = 0
work_end = 480

# Busy intervals for each participant (in minutes after 9:00):

# Catherine's busy intervals:
# 10:30 to 11:00  -> [90, 120)
# 12:30 to 13:30  -> [210, 270)
# 14:30 to 15:00  -> [330, 360)
catherine_busy = [(90, 120), (210, 270), (330, 360)]

# Michael's busy intervals:
# 9:30 to 10:30   -> [30, 90)
# 12:00 to 13:00  -> [180, 240)
# 13:30 to 14:00  -> [270, 300)
# 15:00 to 15:30  -> [360, 390)
michael_busy = [(30, 90), (180, 240), (270, 300), (360, 390)]

# Alexander's busy intervals:
# 9:00 to 9:30    -> [0, 30)
# 10:00 to 10:30  -> [60, 90)
# 11:00 to 12:00  -> [120, 180)
# 13:00 to 13:30  -> [240, 270)
# 14:00 to 16:00  -> [300, 420)
# 16:30 to 17:00  -> [450, 480)
alexander_busy = [(0, 30), (60, 90), (120, 180), (240, 270), (300, 420), (450, 480)]

# Create a Z3 Optimize instance
optimizer = Optimize()

# Define the meeting start time variable (in minutes after 9:00)
S = Int('S')

# The meeting must be scheduled within working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Helper function to ensure that the meeting does not overlap a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for Catherine.
for interval in catherine_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Michael.
for interval in michael_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Alexander.
for interval in alexander_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, choose the earliest possible start time.
optimizer.minimize(S)

# Check for a solution and print the meeting time.
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