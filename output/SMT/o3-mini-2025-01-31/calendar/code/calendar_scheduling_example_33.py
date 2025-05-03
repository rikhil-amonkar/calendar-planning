from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes
meeting_duration = 30

# Define working hours from 9:00 to 17:00.
# Represent time as minutes after 9:00.
work_start = 0
work_end = 480

# Busy intervals for each participant (expressed in minutes after 9:00):

# Lisa's busy intervals:
# 9:00 to 10:00    -> [0, 60)
# 10:30 to 11:30   -> [90, 150)
# 12:30 to 13:00   -> [210, 240)
# 16:00 to 16:30   -> [420, 450)
lisa_busy = [(0, 60), (90, 150), (210, 240), (420, 450)]

# Bobby's busy intervals:
# 9:00 to 9:30    -> [0, 30)
# 10:00 to 10:30  -> [60, 90)
# 11:30 to 12:00  -> [150, 180)
# 15:00 to 15:30  -> [360, 390)
bobby_busy = [(0, 30), (60, 90), (150, 180), (360, 390)]

# Randy's busy intervals:
# 9:30 to 10:00    -> [30, 60)
# 10:30 to 11:00   -> [90, 120)
# 11:30 to 12:30   -> [150, 210)
# 13:00 to 13:30   -> [240, 270)
# 14:30 to 15:30   -> [330, 390)
# 16:00 to 16:30   -> [420, 450)
randy_busy = [(30, 60), (90, 120), (150, 210), (240, 270), (330, 390), (420, 450)]

# Bobby's preference: He prefers to avoid meetings after 15:00.
# We interpret this as the meeting must finish by 15:00. 
# Since 15:00 is 360 minutes after 9:00 and the meeting lasts 30 minutes, we require:
max_start_for_bobby = 360 - meeting_duration  # i.e., S <= 330

# Create a Z3 Optimize instance
optimizer = Optimize()

# Define the meeting start time variable (in minutes after 9:00)
S = Int('S')

# Meeting must lie within working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Bobby's preference: meeting must end by 15:00.
optimizer.add(S <= max_start_for_bobby)

# A helper function to ensure that the meeting does not overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for each busy interval for Lisa.
for interval in lisa_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Bobby.
for interval in bobby_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Randy.
for interval in randy_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, we can minimize S to schedule the meeting at the earliest possible time.
optimizer.minimize(S)

# Check and print the solution.
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