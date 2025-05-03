from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Define working hours: 9:00 to 17:00.
# Represent time as minutes after 9:00 (0 to 480 minutes)
work_start = 0
work_end = 480

# Busy intervals for each participant (expressed in minutes after 9:00):

# Emily is free all day.
emily_busy = []

# Victoria's busy intervals:
# 13:30 to 14:00  -> [270, 300)
# 14:30 to 15:30  -> [330, 390)
# 16:30 to 17:00  -> [450, 480)
victoria_busy = [(270, 300), (330, 390), (450, 480)]

# Nancy's busy intervals:
# 9:00 to 14:00   -> [0, 300)
# 14:30 to 15:30  -> [330, 390)
nancy_busy = [(0, 300), (330, 390)]

# Create a Z3 optimizer instance to enable optimization (earliest meeting)
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00)
S = Int('S')

# The meeting must be scheduled within work hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Define a helper function to ensure no overlap between the meeting interval [s, s+duration) and a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    # Meeting must end before busy interval starts OR start after busy interval ends.
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add non-overlap constraints for each participant's busy intervals.
for interval in emily_busy:
    optimizer.add(no_overlap(S, interval))
for interval in victoria_busy:
    optimizer.add(no_overlap(S, interval))
for interval in nancy_busy:
    optimizer.add(no_overlap(S, interval))

# Since we want the meeting as early as possible, minimize S.
optimizer.minimize(S)

# Check the solution.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes-after-9:00 into HH:MM format.
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