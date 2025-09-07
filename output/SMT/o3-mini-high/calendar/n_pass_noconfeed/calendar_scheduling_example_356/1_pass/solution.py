from z3 import Solver, Int, Or, sat

# Convert hour:minute to minutes from midnight
def time_to_minutes(hour, minute):
    return hour * 60 + minute

# Meeting and work hours parameters
meeting_duration = 30
work_start = time_to_minutes(9, 0)    # 9:00 -> 540 minutes
work_end = time_to_minutes(17, 0)     # 17:00 -> 1020 minutes

# Create Z3 solver
solver = Solver()

# Define meeting start time in minutes after midnight
start = Int('start')

# Basic work hour constraints: meeting must start and finish within work hours
solver.add(start >= work_start)
solver.add(start + meeting_duration <= work_end)

# Angela's preference: avoid meetings before 15:00, so meeting must start at 15:00 or later.
solver.add(start >= time_to_minutes(15, 0))

# Busy intervals for each participant on Monday, in minutes (start, end)
busy_intervals = [
    # Katherine's busy times: 12:00-12:30, 13:00-14:30
    (time_to_minutes(12, 0), time_to_minutes(12, 30)),
    (time_to_minutes(13, 0), time_to_minutes(14, 30)),
    # Julie's busy times: 9:00-9:30, 10:30-11:00, 13:30-14:00, 15:00-15:30
    (time_to_minutes(9, 0), time_to_minutes(9, 30)),
    (time_to_minutes(10, 30), time_to_minutes(11, 0)),
    (time_to_minutes(13, 30), time_to_minutes(14, 0)),
    (time_to_minutes(15, 0), time_to_minutes(15, 30)),
    # Angela's busy times: 9:00-10:00, 10:30-11:00, 11:30-14:00, 14:30-15:00, 16:30-17:00
    (time_to_minutes(9, 0), time_to_minutes(10, 0)),
    (time_to_minutes(10, 30), time_to_minutes(11, 0)),
    (time_to_minutes(11, 30), time_to_minutes(14, 0)),
    (time_to_minutes(14, 30), time_to_minutes(15, 0)),
    (time_to_minutes(16, 30), time_to_minutes(17, 0)),
    # Nicholas's busy times: 9:30-11:00, 11:30-13:30, 14:00-16:00, 16:30-17:00
    (time_to_minutes(9, 30), time_to_minutes(11, 0)),
    (time_to_minutes(11, 30), time_to_minutes(13, 30)),
    (time_to_minutes(14, 0), time_to_minutes(16, 0)),
    (time_to_minutes(16, 30), time_to_minutes(17, 0)),
    # Carl's busy times: 9:00-11:00, 11:30-12:30, 13:00-14:30, 15:00-16:00, 16:30-17:00
    (time_to_minutes(9, 0), time_to_minutes(11, 0)),
    (time_to_minutes(11, 30), time_to_minutes(12, 30)),
    (time_to_minutes(13, 0), time_to_minutes(14, 30)),
    (time_to_minutes(15, 0), time_to_minutes(16, 0)),
    (time_to_minutes(16, 30), time_to_minutes(17, 0))
]

# For each busy interval, ensure that the meeting [start, start+duration)
# does not overlap with the busy interval.
#
# Two intervals [a, b) and [c, d) do not overlap if either:
#   meeting ends (start + duration) <= busy start, or
#   meeting starts (start) >= busy end.
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(start + meeting_duration <= busy_start, start >= busy_end))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + meeting_duration

    # Convert minutes back to HH:MM format
    start_hour = meeting_start // 60
    start_min = meeting_start % 60
    end_hour = meeting_end // 60
    end_min = meeting_end % 60

    meeting_time = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    print("Monday")
    print(meeting_time)
else:
    print("No solution found.")