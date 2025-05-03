from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Define working hours: 9:00 to 17:00.
# Represent time as minutes after 9:00 (i.e., valid times are from 0 to 480 minutes).
work_start = 0
work_end = 480

# Busy intervals for each participant (times represented in minutes after 9:00):

# Gregory's busy intervals:
# 11:00 to 11:30  -> [120, 150)
# 12:00 to 12:30  -> [180, 210)
# 15:30 to 16:30  -> [390, 450)
gregory_busy = [(120, 150), (180, 210), (390, 450)]

# Teresa's busy intervals:
# Teresa is free all day.
teresa_busy = []

# Carol's busy intervals:
# 9:00 to 10:30   -> [0, 90)
# 11:00 to 16:00  -> [120, 420)
# 16:30 to 17:00  -> [450, 480)
carol_busy = [(0, 90), (120, 420), (450, 480)]

# Create a Z3 Optimize instance
optimizer = Optimize()

# Define the meeting start time variable (in minutes after 9:00).
S = Int('S')

# The meeting must occur within working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# A helper function to ensure that a meeting starting at time s 
# does not overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for Gregory.
for interval in gregory_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Teresa.
for interval in teresa_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Carol.
for interval in carol_busy:
    optimizer.add(no_overlap(S, interval))

# (Optional) Schedule the meeting as early as possible by minimizing S.
optimizer.minimize(S)

# Check and extract a solution.
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
    print("End:", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")