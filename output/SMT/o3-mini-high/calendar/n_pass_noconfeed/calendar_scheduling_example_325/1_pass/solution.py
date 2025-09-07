from z3 import *

# Helper function to format minutes into HH:MM string.
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Create the Z3 solver instance.
solver = Solver()

# Define meeting duration in minutes.
duration = 30

# Let 's' be the meeting start time in minutes after midnight.
s = Int('s')

# Working hours: meeting must start no earlier than 9:00 (540) 
# and (due to Jose's preference "no meetings after 15:30") finish by 15:30 (930).
solver.add(s >= 540, s + duration <= 930)

# List all busy intervals (start, end) in minutes for each participant on Monday.
busy_intervals = [
    # Jose's busy times
    (660, 690),   # 11:00 to 11:30
    (750, 780),   # 12:30 to 13:00

    # Keith's busy times
    (840, 870),   # 14:00 to 14:30
    (900, 930),   # 15:00 to 15:30

    # Logan's busy times
    (540, 600),   # 9:00 to 10:00
    (720, 750),   # 12:00 to 12:30
    (900, 930),   # 15:00 to 15:30

    # Megan's busy times
    (540, 630),   # 9:00 to 10:30
    (660, 720),   # 11:00 to 12:00
    (780, 810),   # 13:00 to 13:30
    (870, 990),   # 14:30 to 16:30

    # Gary's busy times
    (540, 570),   # 9:00 to 9:30
    (600, 630),   # 10:00 to 10:30
    (690, 780),   # 11:30 to 13:00
    (810, 840),   # 13:30 to 14:00
    (870, 990),   # 14:30 to 16:30

    # Bobby's busy times
    (660, 690),   # 11:00 to 11:30
    (720, 750),   # 12:00 to 12:30
    (780, 960)    # 13:00 to 16:00
]

# For each busy interval, ensure the meeting does not overlap with it.
# Two intervals [s, s+duration) and [busy_start, busy_end) do not overlap if:
#   s + duration <= busy_start  OR  s >= busy_end
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(s + duration <= busy_start, s >= busy_end))

# Check satisfiability and output a valid meeting time.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[s].as_long()
    meeting_end = meeting_start + duration
    # The day is fixed as Monday.
    day = "Monday"
    # Output the result in the format "HH:MM:HH:MM" along with the day.
    print(f"{day} {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
else:
    print("No meeting time found")