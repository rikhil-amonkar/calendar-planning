from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (1 hour = 60 minutes)
meeting_duration = 60

# Define working hours: 9:00 to 17:00.
# Represent time as minutes after 9:00 (i.e., 0 to 480 minutes).
work_start = 0
work_end = 480

# Additional constraint from Denise: she does not want to meet after 12:30.
# That means the meeting must finish by 12:30.
# 12:30 corresponds to 210 minutes after 9:00 (3.5 hours * 60 = 210).
denise_meeting_deadline = 210

# Busy intervals for each participant (times represented as minutes after 9:00):

# Ryan's busy intervals:
# 9:00 to 9:30 -> [0, 30)
# 12:30 to 13:00 -> [210, 240)
ryan_busy = [(0, 30), (210, 240)]

# Ruth has no busy intervals.
ruth_busy = []

# Denise's busy intervals:
# 9:30 to 10:30 -> [30, 90)
# 12:00 to 13:00 -> [180, 240)
# 14:30 to 16:30 -> [330, 510)
# (Note: The third busy interval doesn't affect the meeting because Denise prefers
# the meeting before 12:30.)
denise_busy = [(30, 90), (180, 240), (330, 510)]

# Create a Z3 Optimize instance
optimizer = Optimize()

# Define the meeting start time variable (in minutes after 9:00)
S = Int('S')

# Meeting must be scheduled within working hours and finish by work_end.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Enforce Denise's constraint: the meeting must finish by 12:30.
optimizer.add(S + meeting_duration <= denise_meeting_deadline)

# Define a helper function to ensure that a meeting starting at time s 
# does not overlap with a provided busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start,  s >= busy_end)

# Add non-overlap constraints for each participant.

# Ryan:
for interval in ryan_busy:
    optimizer.add(no_overlap(S, interval))

# Ruth: (no busy intervals to add)
for interval in ruth_busy:
    optimizer.add(no_overlap(S, interval))

# Denise:
for interval in denise_busy:
    optimizer.add(no_overlap(S, interval))

# Optionally, to schedule the meeting as early as possible (subject to constraints), minimize S.
optimizer.minimize(S)

# Check if a valid meeting slot exists, and print the result.
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