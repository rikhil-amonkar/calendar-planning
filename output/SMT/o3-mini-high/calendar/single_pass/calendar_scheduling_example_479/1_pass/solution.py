from z3 import *

# Meeting duration in minutes
meeting_duration = 60

# Working hours are from 9:00 to 17:00.
# We represent times as minutes offset from 9:00.
# So 9:00 is 0 minutes and 17:00 is 480 minutes.
# The meeting must end by 480, hence start must be at most 420.
start = Int('start')
s = Solver()
s.add(start >= 0, start + meeting_duration <= 480)

# Define busy intervals (in minutes offset from 9:00)
# Each tuple (b_start, b_end) represents a time interval during which a person is busy.
busy_intervals = [
    # Jerry and Jesse:
    (0, 30),       # Busy 9:00 to 9:30
    (90, 180),     # Busy 10:30 to 12:00
    (210, 240),    # Busy 12:30 to 13:00
    (270, 300),    # Busy 13:30 to 14:00
    (330, 360),    # Busy 14:30 to 15:00
    (390, 420),    # Busy 15:30 to 16:00
    # Joshua:
    (120, 210),    # Busy 11:00 to 12:30
    (270, 330),    # Busy 13:30 to 14:30
    (450, 480),    # Busy 16:30 to 17:00
    # Jesse:
    (330, 360),    # (already included above for 14:30 to 15:00)
    (390, 450),    # Busy 15:30 to 16:30
    # Kenneth:
    (90, 210),     # Busy 10:30 to 12:30
    (270, 300),    # Busy 13:30 to 14:00 (already present)
    (330, 360),    # Busy 14:30 to 15:00 (already present)
    (390, 420),    # Busy 15:30 to 16:00 (already present)
    (450, 480)     # Busy 16:30 to 17:00 (already present)
]

# For each busy interval, add a constraint that the meeting does NOT overlap that interval.
# That is, for each busy interval [b_start, b_end):
#   either the meeting finishes on or before b_start: start+meeting_duration <= b_start
#   or it starts on or after b_end: start >= b_end.
for b_start, b_end in busy_intervals:
    s.add(Or(start + meeting_duration <= b_start, start >= b_end))

# Check if there is a solution and extract it.
if s.check() == sat:
    m = s.model()
    meeting_start_offset = m[start].as_long()  # in minutes from 9:00
    meeting_end_offset = meeting_start_offset + meeting_duration

    # Helper function: converts the minutes offset to HH:MM (24-hour format)
    def format_time(offset):
        total_minutes = 9 * 60 + offset  # since 9:00 is our 0
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    day = "Monday"
    start_time = format_time(meeting_start_offset)
    end_time = format_time(meeting_end_offset)

    # Print the solution in the required format.
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found.")