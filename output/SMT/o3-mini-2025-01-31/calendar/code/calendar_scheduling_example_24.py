from z3 import *

# Meeting duration: 30 minutes
meeting_duration = 30

# Working hours: 9:00 to 17:00 (represented as minutes after 9:00, so 0 to 480)
work_start = 0
work_end = 480

# Busy intervals (in minutes after 9:00)
# Benjamin and Hannah are free all day, so their calendars have no busy intervals.
# Brenda's busy intervals are:
#   9:30 to 10:00 -> [30, 60)
#   11:30 to 12:30 -> [150, 210)
#   14:00 to 16:30 -> [300, 450)
brenda_busy = [(30, 60), (150, 210), (300, 450)]

# Create a Z3 solver instance
solver = Solver()

# Define S as the start time of the meeting in minutes after 9:00
S = Int('S')

# Ensure the meeting is scheduled within working hours
solver.add(S >= work_start, S + meeting_duration <= work_end)

# Benjamin's preference: he does not want to meet on Monday after 9:30.
# To ensure that the meeting does not extend past 9:30 (which is 30 minutes after 9:00),
# we add a constraint that the meeting must end by 9:30.
solver.add(S + meeting_duration <= 30)

# For each busy interval of Brenda, ensure the meeting time [S, S+meeting_duration)
# does not overlap with it.
for busy_start, busy_end in brenda_busy:
    solver.add(Or(S + meeting_duration <= busy_start, S >= busy_end))

# Check for a valid meeting slot that meets constraints.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[S].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes after 9:00 into HH:MM format.
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