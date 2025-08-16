from z3 import *

# Create a solver instance
s = Solver()

# Define meeting start time as an integer (minutes after midnight)
start = Int('start')
meeting_duration = 30  # Duration is 30 minutes

# Define work day constraints (Monday 9:00 to 17:00)
# 9:00 AM is 9*60 = 540 minutes and 17:00 is 17*60 = 1020 minutes.
s.add(start >= 540)
s.add(start + meeting_duration <= 1020)

# Nicole's already scheduled meetings:
# Meeting 1: 9:00 to 10:00  -> [540, 600)
# Meeting 2: 10:30 to 16:30 -> [630, 990)
#
# To avoid overlapping a busy interval [busy_start, busy_end),
# the meeting must either finish on or before the busy period starts,
# or start on or after the busy period ends.
#
# (For Meeting 1, this constraint would be either start+30 <= 540 or start >= 600.
# However, Nicole's preference later forces start to be much later, so adding
# this constraint explicitly is optional.)
#
# For Meeting 2, ensure no overlap:
busy_interval_2 = Or(start + meeting_duration <= 630, start >= 990)
s.add(busy_interval_2)

# Nicole's preference: she would rather not meet on Monday before 16:00.
# 16:00 is 16*60 = 960 minutes.
s.add(start >= 960)

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + meeting_duration

    # Function to convert minutes to HH:MM format
    def minutes_to_time_str(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours:02d}:{minutes:02d}"

    # The meeting is on Monday
    day = "Monday"
    start_time_str = minutes_to_time_str(meeting_start)
    end_time_str = minutes_to_time_str(meeting_end)

    # Print solution in the required format:
    output = (
        "SOLUTION:\n"
        f"Day: {day}\n"
        f"Start Time: {start_time_str}\n"
        f"End Time: {end_time_str}"
    )
    print(output)
else:
    print("No solution found.")