from z3 import *

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Meeting duration in minutes
meeting_duration = 30

# Create a Z3 solver instance
solver = Solver()

# Declare an integer variable for the meeting start time (in minutes from midnight)
meeting_start = Int("meeting_start")

# Working hours: meeting must start no earlier than 9:00 (540 minutes)
# and finish no later than 17:00 (1020 minutes)
solver.add(meeting_start >= 9 * 60)
solver.add(meeting_start + meeting_duration <= 17 * 60)

# Henry's preference: prefer to meet before 10:00 (i.e. the meeting must finish by 10:00, or at most start at 9:30)
solver.add(meeting_start + meeting_duration <= 10 * 60)

# Eric's busy intervals on Monday (in minutes)
# Eric is busy from 12:00 to 13:00 and 14:00 to 15:00.
eric_busy = [(12 * 60, 13 * 60), (14 * 60, 15 * 60)]
for start, end in eric_busy:
    # The meeting must either finish before an existing busy interval or start after it ends.
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Henry's busy intervals on Monday (in minutes)
# Henry has meetings during:
#  9:30 to 10:00, 10:30 to 11:00, 11:30 to 12:30,
#  13:00 to 13:30, 14:30 to 15:00, and 16:00 to 17:00.
henry_busy = [
    (9 * 60 + 30, 10 * 60),
    (10 * 60 + 30, 11 * 60),
    (11 * 60 + 30, 12 * 60 + 30),
    (13 * 60, 13 * 60 + 30),
    (14 * 60 + 30, 15 * 60),
    (16 * 60, 17 * 60)
]
for start, end in henry_busy:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if a solution exists and output the meeting time along with the day of the week.
if solver.check() == sat:
    model = solver.model()
    start = model[meeting_start].as_long()
    end = start + meeting_duration
    day = "Monday"
    print(day)
    print(f"{format_time(start)}:{format_time(end)}")
else:
    print("No valid meeting time found.")