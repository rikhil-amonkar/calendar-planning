from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (half an hour = 30 minutes)
meeting_duration = 30

# Work hours: 9:00 mapped to 0 and 17:00 mapped to 480 (minutes after 9:00)
work_start = 0
work_end = 480

# Helper conversion (minutes after 9:00):
# 9:00   -> 0
# 11:30  -> 150
# 12:00  -> 180
# 12:30  -> 210
# 13:00  -> 240
# 14:00  -> 300
# 14:30  -> 330
# 15:00  -> 360
# 15:30  -> 390
# 16:00  -> 420
# 17:00  -> 480

# Denise's busy intervals (in minutes after 9:00):
#   12:00 to 12:30 -> [180, 210)
#   15:30 to 16:00 -> [390, 420)
denise_busy = [(180, 210), (390, 420)]

# Angela has no meetings so no busy intervals for her.
angela_busy = []

# Natalie's busy intervals:
#   9:00 to 11:30  -> [0, 150)
#   12:00 to 13:00 -> [180, 240)
#   14:00 to 14:30 -> [300, 330)
#   15:00 to 17:00 -> [360, 480)
natalie_busy = [(0, 150), (180, 240), (300, 330), (360, 480)]

# Create an optimizer instance.
optimizer = Optimize()

# Define the meeting start time S (in minutes after 9:00)
S = Int('S')

# The meeting must be within the work hours.
optimizer.add(S >= work_start)
optimizer.add(S + meeting_duration <= work_end)

# Helper function to ensure the meeting does not overlap with a busy interval.
def no_overlap(s, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

# Add constraints for Denise
for interval in denise_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Angela (none, but keeping for structure)
for interval in angela_busy:
    optimizer.add(no_overlap(S, interval))

# Add constraints for Natalie.
for interval in natalie_busy:
    optimizer.add(no_overlap(S, interval))

# To meet at the earliest availability, we minimize S.
optimizer.minimize(S)

# Check for satisfiability and print the solution.
if optimizer.check() == sat:
    model = optimizer.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Convert minutes after 9:00 to HH:MM format.
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