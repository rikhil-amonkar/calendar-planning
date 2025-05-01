from z3 import *

# Meeting duration in minutes
meeting_duration = 60

# Work day: 9:00 to 17:00 => times in minutes with 9:00 = 0 and 17:00 = 480.
work_start = 0
work_end = 480

# Declare a variable for the meeting start (in minutes after 9:00).
s = Int('s')

solver = Solver()

# The meeting must start in a time window that allows a full 60 minute meeting.
solver.add(s >= work_start, s + meeting_duration <= work_end)

# Define busy intervals (in minutes after 9:00) for each person:

# Michelle: has a meeting 11:00 to 12:00 -> 120 to 180.
busy_intervals = [
    (120, 180),  # Michelle

    # Steven:
    (0, 30),     # 9:00 to 9:30
    (150, 180),  # 11:30 to 12:00
    (270, 300),  # 13:30 to 14:00
    (390, 420),  # 15:30 to 16:00

    # Jerry:
    (0, 30),     # 9:00 to 9:30
    (60, 120),   # 10:00 to 11:00
    (150, 210),  # 11:30 to 12:30
    (240, 330),  # 13:00 to 14:30
    (390, 420),  # 15:30 to 16:00
    (450, 480)   # 16:30 to 17:00
]

# For each busy interval [b_start, b_end],
# the meeting [s, s+60) must either finish before b_start or start after b_end.
def no_overlap(b_start, b_end):
    return Or(s + meeting_duration <= b_start, s >= b_end)

for (b_start, b_end) in busy_intervals:
    solver.add(no_overlap(b_start, b_end))

# Check if a solution exists
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[s].as_long()  # minutes after 9:00
    # convert meeting_start to HH:MM format
    hour = 9 + meeting_start // 60
    minute = meeting_start % 60
    meeting_time_str = f"{hour:02d}:{minute:02d}"
    print("A valid meeting start time is:", meeting_time_str)
else:
    print("No valid meeting time found.")