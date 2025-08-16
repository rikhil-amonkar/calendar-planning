from z3 import Int, Or, Solver

# Helper function to convert minutes since midnight to "HH:MM" string format.
def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

# Meeting duration in minutes
duration = 30

# Define working hours for Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
working_start = 9 * 60      # 540
working_end = 17 * 60       # 1020

# Create an integer variable "start" representing the meeting start time in minutes since midnight.
start = Int('start')

# Create a solver instance and add the domain constraint for the meeting start.
s = Solver()
s.add(start >= working_start, start + duration <= working_end)

# Define the busy intervals for each participant in minutes since midnight.
# Each tuple is (busy_start, busy_end). Meetings may border, so equality is allowed.
busy_intervals = [
    # Joe's busy times
    (570, 600),    # 9:30 to 10:00
    (630, 660),    # 10:30 to 11:00

    # Keith's busy times
    (690, 720),    # 11:30 to 12:00
    (900, 930),    # 15:00 to 15:30

    # Patricia's busy times
    (540, 570),    # 9:00 to 9:30
    (780, 810),    # 13:00 to 13:30

    # Nancy's busy times
    (540, 660),    # 9:00 to 11:00
    (690, 990),    # 11:30 to 16:30

    # Pamela's busy times
    (540, 600),    # 9:00 to 10:00
    (630, 660),    # 10:30 to 11:00
    (690, 750),    # 11:30 to 12:30
    (780, 840),    # 13:00 to 14:00
    (870, 900),    # 14:30 to 15:00
    (930, 960),    # 15:30 to 16:00
    (990, 1020)    # 16:30 to 17:00
]

# For each busy interval, ensure that the meeting does NOT overlap with it.
# A meeting [start, start+duration) is conflict free with a busy interval [b_start, b_end)
# if it ends at or before b_start, or starts at or after b_end.
for b_start, b_end in busy_intervals:
    s.add(Or(start + duration <= b_start, start >= b_end))

# Check for a solution.
if s.check() == sat:
    model = s.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + duration
    # Print the solution in the required format.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", minutes_to_time(meeting_start))
    print("End Time:", minutes_to_time(meeting_end))
else:
    print("No valid meeting time found.")