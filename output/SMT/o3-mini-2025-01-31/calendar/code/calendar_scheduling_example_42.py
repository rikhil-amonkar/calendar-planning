from z3 import Optimize, Int, Or, sat

# Meeting duration in minutes (60 minutes)
meeting_duration = 60

# Define working hours: 9:00 to 17:00.
# Represent time as minutes after 9:00, so the window is from 0 to 480 minutes.
work_start = 0
work_end = 480

# Define participants' busy intervals (in minutes after 9:00):

# Julie's busy intervals:
# 9:00 to 9:30 -> [0, 30)
# 11:00 to 11:30 -> [120, 150)
# 12:00 to 12:30 -> [180, 210)
# 13:30 to 14:00 -> [270, 300)
# 16:00 to 17:00 -> [420, 480)
julie_busy = [(0, 30), (120, 150), (180, 210), (270, 300), (420, 480)]

# Sean's busy intervals:
# 9:00 to 9:30 -> [0, 30)
# 13:00 to 13:30 -> [240, 270)
# 15:00 to 15:30 -> [360, 390)
# 16:00 to 16:30 -> [420, 450)
sean_busy = [(0, 30), (240, 270), (360, 390), (420, 450)]

# Lori's busy intervals:
# 10:00 to 10:30 -> [60, 90)
# 11:00 to 13:00 -> [120, 240)
# 15:30 to 17:00 -> [390, 480)
lori_busy = [(60, 90), (120, 240), (390, 480)]

# Initialize an optimizer.
optimizer = Optimize()

# Define the meeting start time variable (in minutes after 9:00).
S = Int('S')

# Ensure the meeting is within working hours.
optimizer.add(S >= work_start, S + meeting_duration <= work_end)

# Helper function that returns a constraint ensuring that the meeting interval [S, S+meeting_duration)
# does not overlap with a given busy interval.
def no_overlap(s, busy_interval):
    b_start, b_end = busy_interval
    return Or(s + meeting_duration <= b_start, s >= b_end)

# Add non-overlap constraints for Julie's busy intervals.
for interval in julie_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Sean's busy intervals.
for interval in sean_busy:
    optimizer.add(no_overlap(S, interval))

# Add non-overlap constraints for Lori's busy intervals.
for interval in lori_busy:
    optimizer.add(no_overlap(S, interval))

# To meet a preference for the earliest possible meeting, we minimize the start time S.
optimizer.minimize(S)

# Check if constraints are satisfiable and print the meeting time if a solution is found.
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
    print("End:  ", minutes_to_time(meeting_end))
else:
    print("No valid meeting slot can be found.")