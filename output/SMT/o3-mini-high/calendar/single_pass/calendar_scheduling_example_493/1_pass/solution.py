from z3 import *

# Define a Z3 integer to represent the meeting start time in minutes from midnight.
# Since work hours are 9:00 (540 minutes) to 17:00 (1020 minutes),
# and the meeting duration is 30 minutes, we require: 540 <= start_time <= 990.
start_time = Int("start_time")
meeting_duration = 30

solver = Solver()
solver.add(start_time >= 540, start_time + meeting_duration <= 1020)

# Busy intervals for participants are given as tuples (busy_start, busy_end) in minutes.
# Converting times to minutes (24-hour clock):
#   9:00  -> 540,  9:30  -> 570, 10:00 -> 600, 10:30 -> 630, 11:00 -> 660, 11:30 -> 690,
#   12:00 -> 720, 12:30 -> 750, 13:00 -> 780, 13:30 -> 810, 14:00 -> 840, 14:30 -> 870,
#   15:00 -> 900, 15:30 -> 930, 16:00 -> 960, 16:30 -> 990, 17:00 -> 1020
busy_intervals = [
    # Stephanie's busy intervals
    (660, 690),   # 11:00-11:30
    (870, 900),   # 14:30-15:00

    # Joe's busy intervals
    (540, 570),   # 9:00-9:30
    (600, 720),   # 10:00-12:00
    (750, 780),   # 12:30-13:00
    (840, 1020),  # 14:00-17:00

    # Diana's busy intervals
    (540, 630),   # 9:00-10:30
    (690, 720),   # 11:30-12:00
    (780, 840),   # 13:00-14:00
    (870, 930),   # 14:30-15:30
    (960, 1020),  # 16:00-17:00

    # Deborah's busy intervals
    (540, 600),   # 9:00-10:00
    (630, 720),   # 10:30-12:00
    (750, 780),   # 12:30-13:00
    (810, 840),   # 13:30-14:00
    (870, 930),   # 14:30-15:30
    (960, 990)    # 16:00-16:30
]

# For each busy interval, the meeting (from start_time to start_time+30) must not overlap.
# This is enforced by ensuring for every interval (a, b):
#   either the meeting ends on or before the busy interval starts, or 
#   it starts on or after the busy interval ends.
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check for a solution.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes to HH:MM format.
    def minutes_to_HHMM(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    day = "Monday"
    start_str = minutes_to_HHMM(meeting_start)
    end_str = minutes_to_HHMM(meeting_end)

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_str}")
    print(f"End Time: {end_str}")
else:
    print("No solution found.")